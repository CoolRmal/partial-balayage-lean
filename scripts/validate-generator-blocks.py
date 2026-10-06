#!/usr/bin/env python3
"""Build immutable actual square data with Lean; Python supplies no proof checks."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path.cwd()
OUT = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "square-numerical"
DOWNLOAD = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "square-numerical-download"
PREFIX = "PartialBalayage.Maximal.Square.Data.GeneratorLeafBlocks"
NAMESPACE = "PartialBalayage.Maximal.Square"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "c55e6e786f49471c72fbddbec5415808896aec1e"
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^(?:(?:public|meta)\s+)*import\s+(\S+)", re.MULTILINE)
AXIOMS = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|"
    r"does not depend on any axioms)", re.MULTILINE)


def command(args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for piece in iter(lambda: f.read(1024 * 1024), b""):
            h.update(piece)
    return h.hexdigest()


def save_json(name, value):
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def source_hashes():
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "*.lean", "lean-toolchain", "lakefile.toml",
         "lake-manifest.json", "scripts/validate-generator-blocks.py"], cwd=ROOT)
    return {name: digest(ROOT / name) for name in
            names.decode().split("\0") if name}


def inspect(runtime=False):
    expected = os.environ["NUMERICAL_COMMIT"]
    if not re.fullmatch(r"[0-9a-f]{40}", expected):
        raise ValueError("NUMERICAL_COMMIT must be a full lower-case public SHA")
    actual = command(["git", "rev-parse", "HEAD"])
    if actual != expected:
        raise ValueError(f"Checkout {actual} differs from requested snapshot {expected}")
    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError("Unexpected Lean toolchain")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    if next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib") != MATHLIB:
        raise ValueError("Unexpected mathlib manifest pin")
    lakefile = (ROOT / "lakefile.toml").read_text()
    if f'rev = "{MATHLIB}"' not in lakefile:
        raise ValueError("The lakefile differs from the pinned manifest")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "*.lean",
                    "lean-toolchain", "lakefile.toml", "lake-manifest.json"],
                   cwd=ROOT, check=True)
    hashes = source_hashes()
    for block in range(106):
        path = ROOT / (PREFIX.replace(".", "/") + f"{block}.lean")
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"Missing regular candidate file: {path}")
        if str(path.relative_to(ROOT)) not in hashes:
            raise ValueError(f"Candidate is absent from the requested public commit: {path}")
        if f"theorem generatorLeafBlocks{block}_valid" not in path.read_text():
            raise ValueError(f"Missing actual public validity endpoint: {path}")
    if runtime:
        if command(["lake", "env", "lean", "--githash"]) != LEAN_COMMIT:
            raise ValueError("Installed Lean does not have the pinned release commit")
        if command(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]) != MATHLIB:
            raise ValueError("Installed mathlib differs from the pin")
    report = {"commit": actual, "toolchain": TOOLCHAIN, "lean_commit": LEAN_COMMIT,
              "mathlib": MATHLIB, "source_hashes": hashes}
    save_json("snapshot.json", report)
    return report


def check_immutable(snapshot):
    if snapshot["source_hashes"] != source_hashes():
        raise ValueError("Tracked mathematical sources changed during validation")


def timed_run(args, stem):
    OUT.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    with (OUT / f"{stem}.log").open("w") as log:
        run = subprocess.run(["/usr/bin/time", "-v", "-o", str(OUT / f"{stem}.time"),
                              *args], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    seconds = time.monotonic() - start
    print(f"{stem}: exit {run.returncode}, {seconds:.1f}s", flush=True)
    if run.returncode:
        raise RuntimeError(f"{stem} failed; inspect its uploaded log")
    return seconds


def audit(path, expected, stem):
    seconds = timed_run(["lake", "env", "lean", "--threads=2", "--memory=8192",
                         str(path)], stem)
    text = (OUT / f"{stem}.log").read_text()
    found = {m.group(1): {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
             for m in AXIOMS.finditer(text)}
    for name in expected:
        if name not in found:
            raise ValueError(f"Missing imported axiom audit for {name}")
        if not found[name] <= PERMITTED:
            raise ValueError(f"Unpermitted axioms for {name}: {found[name] - PERMITTED}")
    return {"seconds": seconds, "axioms": {n: sorted(found[n]) for n in expected}}


def shared_modules():
    imports = set()
    for block in range(106):
        path = ROOT / (PREFIX.replace(".", "/") + f"{block}.lean")
        imports.update(IMPORT.findall(path.read_text()))
    fast = f"{NAMESPACE}.GeneratorLeafFastCheck"
    sparse = f"{NAMESPACE}.GeneratorLeafSparseCheck"
    fixed = [fast, f"{NAMESPACE}.GeneratorRadialRoots",
             f"{NAMESPACE}.GeneratorPartitionRectangles"]
    if sparse in imports:
        fixed.append(sparse)
    coordinates = sorted((m for m in imports if ".Data.GeneratorCoordinates" in m),
                         key=lambda m: int(m.rsplit("GeneratorCoordinates", 1)[1]))
    if not imports <= set(fixed + coordinates) or not (
            set(fixed[1:3]) <= imports and ({fast, sparse} & imports)):
        raise ValueError(f"Unexpected leaf imports: {sorted(imports - set(fixed + coordinates))}")
    return fixed + coordinates


def warm():
    snapshot = inspect(runtime=True)
    modules = shared_modules()
    report = {"snapshot": snapshot, "modules": [], "status": "building"}
    for module in modules:
        seconds = timed_run(["lake", "build", module], f"warm-{module.rsplit('.', 1)[1]}")
        report["modules"].append({"module": module, "seconds": seconds})
        save_json("warm-report.json", report)
    endpoints = [f"{NAMESPACE}.generatorRadialRoots_valid"]
    if f"{NAMESPACE}.GeneratorLeafSparseCheck" in modules:
        endpoints.extend(f"{NAMESPACE}.{name}" for name in [
            "sparseScaleInterval_eq", "sparseProduct_eq", "sparseGeneratorTensorIntervals_eq",
            "sparseGeneratorApproximationIntervals_eq", "sparseGeneratorApproximationError_eq",
            "sparseGeneratorCombinedIntervals_eq",
            "GeneratorLeafData.sparseLowerBound_eq_fastLowerBound",
            "GeneratorLeafData.sparseLowerBound_eq_lowerBound",
            "GeneratorLeafData.numericalValid_of_sparse",
        ])
    for module in modules:
        if ".Data.GeneratorCoordinates" in module:
            source = ROOT / (module.replace(".", "/") + ".lean")
            endpoints.extend(f"{NAMESPACE}.{name}" for name in
                             re.findall(r"theorem\s+(generatorCoordinates\d+_valid)",
                                        source.read_text()))
    endpoints = sorted(set(endpoints))
    path = OUT / "warm-audit.lean"
    path.write_text("\n".join([*(f"import {m}" for m in modules), "",
                              *(f"#print axioms {n}" for n in endpoints), ""]))
    report["audit"] = audit(path, endpoints, "warm-audit")
    check_immutable(snapshot)
    outputs = []
    for directory in (ROOT / ".lake/build/lib/lean", ROOT / ".lake/build/ir"):
        for path in sorted(directory.rglob("*")):
            if path.is_file() and not path.is_symlink() and path.name.endswith(
                    (".olean", ".olean.private", ".olean.server", ".ilean", ".ir",
                     ".ir.sig", ".c", ".bc", ".trace", ".hash")):
                if "GeneratorLeafBlocks" not in path.name:
                    outputs.append(path)
    listing = OUT / "warm-files.txt"
    listing.write_text("\n".join(str(p.relative_to(ROOT)) for p in outputs) + "\n")
    archive = OUT / "warm-outputs.tar.zst"
    subprocess.run(["tar", "-I", "zstd -T2 -3", "-cf", str(archive),
                    "-T", str(listing)], cwd=ROOT, check=True)
    manifest = {**snapshot, "artifact_output_count": len(outputs),
                "uncompressed_bytes": sum(p.stat().st_size for p in outputs),
                "archive_sha256": digest(archive), "archive_bytes": archive.stat().st_size}
    save_json("warm-manifest.json", manifest)
    report["status"] = "pass"
    save_json("warm-report.json", report)
    print(f"Warm archive: {archive.stat().st_size} bytes, {len(outputs)} required outputs")


def restore():
    snapshot = inspect(runtime=True)
    manifest = json.loads((DOWNLOAD / "warm-manifest.json").read_text())
    for key in ("commit", "toolchain", "lean_commit", "mathlib", "source_hashes"):
        if manifest[key] != snapshot[key]:
            raise ValueError(f"Warm artifact differs from this immutable snapshot: {key}")
    archive = DOWNLOAD / "warm-outputs.tar.zst"
    if digest(archive) != manifest["archive_sha256"]:
        raise ValueError("Warm archive checksum mismatch")
    subprocess.run(["tar", "--zstd", "-xf", str(archive)], cwd=ROOT, check=True)
    check_immutable(snapshot)
    save_json("restored-warm-manifest.json", manifest)


def block_audit(block):
    name = f"generatorLeafBlocks{block}"
    valid = f"{NAMESPACE}.{name}_valid"
    numerical = f"SquareNumericalAudit.block{block}_numericalValid"
    positive = f"SquareNumericalAudit.block{block}_pointwise_positive"
    path = OUT / f"block-{block}-audit.lean"
    path.write_text(f"""import {PREFIX}{block}
open PartialBalayage.Maximal.Square
namespace SquareNumericalAudit
theorem block{block}_numericalValid (i : Fin 64) :
    ({name} i).NumericalValid :=
  ({name}_valid i).2.2.2
theorem block{block}_pointwise_positive (i : Fin 64) {{u v : ℝ}}
    (h : ({name} i).rectangle.Contains u v)
    (hu : 0 < u) (hv : 0 < v) (hr : u + v < 28) :
    0 < generatorInteriorDensity u v :=
  GeneratorLeafData.positivity ({name}_valid i) h hu hv hr
#print axioms {valid}
#print axioms {numerical}
#print axioms {positive}
end SquareNumericalAudit
""")
    return audit(path, [valid, numerical, positive], f"block-{block}-audit")


def run_range():
    snapshot = inspect(runtime=True)
    first, last = int(os.environ["NUMERICAL_FIRST"]), int(os.environ["NUMERICAL_LAST"])
    if not 0 <= first <= last < 106:
        raise ValueError("Invalid fixed block range")
    report = {"snapshot": snapshot, "first": first, "last": last,
              "blocks": [], "status": "building"}
    save_json("range-report.json", report)
    for block in range(first, last + 1):
        check_immutable(snapshot)
        record = {"block": block, "module": PREFIX + str(block), "status": "building"}
        report["blocks"].append(record)
        save_json("range-report.json", report)
        record["build_seconds"] = timed_run(["lake", "build", PREFIX + str(block)],
                                            f"block-{block}-build")
        record["audit"] = block_audit(block)
        record["status"] = "pass"
        save_json("range-report.json", report)
    check_immutable(snapshot)
    report["status"] = "pass"
    save_json("range-report.json", report)


if __name__ == "__main__":
    OUT.mkdir(parents=True, exist_ok=True)
    modes = {"inspect": inspect, "warm": warm, "restore": restore, "range": run_range}
    if len(sys.argv) != 2 or sys.argv[1] not in modes:
        raise SystemExit("Usage: validate-generator-blocks.py inspect|warm|restore|range")
    modes[sys.argv[1]]()
