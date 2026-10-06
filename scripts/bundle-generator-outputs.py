#!/usr/bin/env python3
"""Retain genuine Lean build outputs from the immutable square-check matrix.

Run this control script from its separate dispatcher checkout, with the current
directory set to the mathematical candidate checkout.  It never edits sources
or invokes a proof build.  The existing range driver must already have built and
audited every exported proof before ``pack`` accepts that range.

Bundles are a build cache, not a replacement for the final source-based Palomar
check.  Restore on the same pinned Ubuntu environment first; native compilation
or differing local traces can still require rebuilding on another platform.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile

FORMAT = "square-generator-build-outputs-v1"
PREFIX = "PartialBalayage.Maximal.Square.Data.GeneratorLeafBlocks"
NAMESPACE = "PartialBalayage.Maximal.Square"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "c55e6e786f49471c72fbddbec5415808896aec1e"
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
RANGES = [(n, min(n + 5, 105)) for n in range(0, 106, 6)]
ARTIFACT_SUFFIXES = (
    ".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig",
    ".c", ".bc", ".trace", ".hash",
)
BASES = (".lake/build/lib/lean/", ".lake/build/ir/")
ROOT = Path.cwd().resolve()
OUT = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "square-numerical"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def source_hashes():
    names = subprocess.check_output([
        "git", "ls-files", "-z", "*.lean", "lean-toolchain", "lakefile.toml",
        "lake-manifest.json", "scripts/validate-generator-blocks.py",
    ], cwd=ROOT).decode().split("\0")
    return {name: digest(ROOT / name) for name in names if name}


def snapshot():
    expected = os.environ["NUMERICAL_COMMIT"]
    control = os.environ["CONTROL_COMMIT"]
    for name, value in (("NUMERICAL_COMMIT", expected), ("CONTROL_COMMIT", control)):
        require(re.fullmatch(r"[0-9a-f]{40}", value), f"Invalid full SHA: {name}")
    require(command(["git", "rev-parse", "HEAD"]) == expected,
            "The outer checkout differs from the immutable candidate SHA")
    control_root = Path(__file__).resolve().parent.parent
    require(command(["git", "rev-parse", "HEAD"], control_root) == control,
            "The control script checkout differs from CONTROL_COMMIT")
    relative_script = Path(__file__).resolve().relative_to(control_root)
    committed_script = subprocess.check_output(
        ["git", "show", f"{control}:{relative_script.as_posix()}"], cwd=control_root)
    require(hashlib.sha256(committed_script).hexdigest() == digest(Path(__file__).resolve()),
            "The running control script differs from its committed source")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", str(relative_script)],
                   cwd=control_root, check=True)
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Unexpected Lean toolchain")
    manifest = read_json(ROOT / "lake-manifest.json")
    rev = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    require(rev == MATHLIB, "Unexpected mathlib manifest pin")
    require(f'rev = "{MATHLIB}"' in (ROOT / "lakefile.toml").read_text(),
            "The lakefile differs from the pinned mathlib manifest")
    require(command(["lake", "env", "lean", "--githash"]) == LEAN_COMMIT,
            "The installed Lean differs from the pinned release commit")
    require(command(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]) == MATHLIB,
            "The installed mathlib differs from the source pin")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "*.lean",
                    "lean-toolchain", "lakefile.toml", "lake-manifest.json"],
                   cwd=ROOT, check=True)
    return {
        "commit": expected, "toolchain": TOOLCHAIN, "lean_commit": LEAN_COMMIT,
        "mathlib": MATHLIB, "source_hashes": source_hashes(),
    }


def same_snapshot(actual, expected, context):
    for key in ("commit", "toolchain", "lean_commit", "mathlib", "source_hashes"):
        require(actual.get(key) == expected[key], f"{context} differs in {key}")


def check_immutable(before):
    require(source_hashes() == before["source_hashes"],
            "Tracked mathematical sources changed during bundling/restoration")


def safe_name(name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and "\\" not in name,
            f"Unsafe archive path: {name}")
    require(str(path) == name and any(name.startswith(base) for base in BASES),
            f"Unexpected build-output path: {name}")
    require(name.endswith(ARTIFACT_SUFFIXES), f"Unexpected build-output suffix: {name}")
    return path


def module_paths(block):
    relative = PREFIX.replace(".", "/") + str(block)
    return ROOT / BASES[0] / relative, ROOT / BASES[1] / relative


def block_outputs(block):
    library, ir = module_paths(block)
    paths = []
    for stem in (library, ir):
        for path in sorted(stem.parent.glob(stem.name + ".*")):
            if path.name.endswith(ARTIFACT_SUFFIXES):
                require(path.is_file() and not path.is_symlink(),
                        f"Nonregular build output: {path}")
                paths.append(path)
    names = {str(path.relative_to(ROOT)) for path in paths}
    required = [library.with_suffix(library.suffix + suffix) for suffix in
                (".trace", ".olean", ".olean.hash", ".ilean", ".ilean.hash")]
    required += [ir.with_suffix(ir.suffix + suffix) for suffix in (".c", ".c.hash")]
    trace = read_json(library.with_suffix(library.suffix + ".trace"))
    outputs = trace.get("outputs", {})
    require(outputs.get("m") is True and len(outputs.get("o", [])) == 3,
            f"Missing actual three-part module output description for block {block}")
    required += [library.with_suffix(library.suffix + suffix) for suffix in
                 (".olean.server", ".olean.server.hash",
                  ".olean.private", ".olean.private.hash")]
    for key, suffix in (("rs", ".ir.sig"), ("r", ".ir")):
        if outputs.get(key):
            required += [library.with_suffix(library.suffix + suffix),
                         library.with_suffix(library.suffix + suffix + ".hash")]
    for path in required:
        require(str(path.relative_to(ROOT)) in names, f"Missing required output: {path}")
    return paths


def check_bundled_block_outputs(outputs, block):
    library, ir = module_paths(block)
    required = [str(path.relative_to(ROOT)) for path in
                [library.with_suffix(library.suffix + suffix) for suffix in
                 (".trace", ".olean", ".olean.hash", ".ilean", ".ilean.hash",
                  ".olean.server", ".olean.server.hash",
                  ".olean.private", ".olean.private.hash")]]
    required += [str(ir.with_suffix(ir.suffix + suffix).relative_to(ROOT))
                 for suffix in (".c", ".c.hash")]
    require(set(required) <= set(outputs),
            f"The bundle is missing required module outputs for block {block}")


def check_range_report(report, first, last, source):
    same_snapshot(report["snapshot"], source, "The range driver report")
    require(report.get("status") == "pass", "The range driver has not completed successfully")
    require((report.get("first"), report.get("last")) == (first, last),
            "The range driver report has different boundaries")
    records = report.get("blocks", [])
    require([r.get("block") for r in records] == list(range(first, last + 1)),
            "The range driver report does not cover every block exactly once")
    for record in records:
        block = record["block"]
        require(record.get("status") == "pass" and record.get("module") == PREFIX + str(block),
                f"Block {block} has not completed its actual build/audit")
        expected = {
            f"{NAMESPACE}.generatorLeafBlocks{block}_valid",
            f"SquareNumericalAudit.block{block}_numericalValid",
            f"SquareNumericalAudit.block{block}_pointwise_positive",
        }
        axioms = record.get("audit", {}).get("axioms", {})
        require(set(axioms) == expected, f"Missing genuine imported proof audits for block {block}")
        for theorem, basis in axioms.items():
            require(set(basis) <= PERMITTED, f"Unpermitted axioms in {theorem}")


def pack(first, last):
    require((first, last) in RANGES, "The range is not one of the fixed 18 matrix ranges")
    source = snapshot()
    report = read_json(OUT / "range-report.json")
    check_range_report(report, first, last, source)
    warm = read_json(OUT / "restored-warm-manifest.json")
    same_snapshot(warm, source, "The restored warm manifest")
    paths = [path for block in range(first, last + 1) for path in block_outputs(block)]
    inventory = {
        str(path.relative_to(ROOT)): {"sha256": digest(path), "bytes": path.stat().st_size}
        for path in paths
    }
    archive = OUT / f"range-outputs-{first}-{last}.tar.gz"
    with tarfile.open(archive, "w:gz", compresslevel=3) as tar:
        for path in paths:
            tar.add(path, arcname=str(path.relative_to(ROOT)), recursive=False)
    check_immutable(source)
    for path in paths:
        require(digest(path) == inventory[str(path.relative_to(ROOT))]["sha256"],
                f"A build output changed while it was being archived: {path}")
    manifest = {
        "format": FORMAT, "snapshot": source, "control_commit": os.environ["CONTROL_COMMIT"],
        "first": first, "last": last, "range_report": report,
        "warm_archive_sha256": warm["archive_sha256"],
        "archive": archive.name, "archive_sha256": digest(archive),
        "archive_bytes": archive.stat().st_size, "outputs": inventory,
    }
    manifest_path = OUT / f"range-manifest-{first}-{last}.json"
    write_json(manifest_path, manifest)
    print(f"Packed genuine validated blocks {first}-{last}: {len(paths)} outputs, "
          f"{archive.stat().st_size} archive bytes", flush=True)


def archive_members(archive, visit):
    if archive.name.endswith(".tar.zst"):
        process = subprocess.Popen(["zstd", "--decompress", "--stdout", str(archive)],
                                   stdout=subprocess.PIPE)
        try:
            with tarfile.open(fileobj=process.stdout, mode="r|") as tar:
                for member in tar:
                    visit(tar, member)
            require(process.wait() == 0, "Warm archive decompression failed")
        finally:
            process.stdout.close()
            if process.poll() is None:
                process.terminate()
                process.wait()
    else:
        with tarfile.open(archive, "r:gz") as tar:
            for member in tar:
                visit(tar, member)


def inspect_archive(archive, expected=None):
    inventory = {}

    def visit(tar, member):
        safe_name(member.name)
        require(member.isfile() and not member.issym() and not member.islnk(),
                f"Nonregular archive member: {member.name}")
        require(member.name not in inventory, f"Duplicate archive member: {member.name}")
        h = hashlib.sha256()
        with tar.extractfile(member) as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                h.update(chunk)
        inventory[member.name] = {"sha256": h.hexdigest(), "bytes": member.size}

    archive_members(archive, visit)
    if expected is not None:
        require(inventory == expected, f"Archive members differ from their hashes: {archive}")
    return inventory


def range_member_block(name):
    safe_name(name)
    relative = name.removeprefix(BASES[0]).removeprefix(BASES[1])
    match = re.fullmatch(re.escape(PREFIX.replace(".", "/")) + r"(\d+)\..+", relative)
    require(match is not None, f"Non-leaf member in a range artifact: {name}")
    return int(match.group(1))


def validate_all(download):
    source = snapshot()
    warm_pairs = [(p, p.with_name("warm-outputs.tar.zst"))
                  for p in download.rglob("warm-manifest.json")
                  if p.with_name("warm-outputs.tar.zst").is_file()]
    require(len(warm_pairs) == 1, "Expected exactly one paired warm manifest/archive")
    warm_path, warm_archive = warm_pairs[0]
    require(not warm_archive.is_symlink(), "The warm archive must be a regular file")
    warm = read_json(warm_path)
    same_snapshot(warm, source, "The downloaded warm manifest")
    require(digest(warm_archive) == warm["archive_sha256"], "Warm archive checksum mismatch")
    require(warm_archive.stat().st_size == warm["archive_bytes"], "Warm archive size mismatch")
    warm_outputs = inspect_archive(warm_archive)
    require(len(warm_outputs) == warm["artifact_output_count"], "Warm output count mismatch")
    require(sum(r["bytes"] for r in warm_outputs.values()) == warm["uncompressed_bytes"],
            "Warm uncompressed byte count mismatch")
    require(all("GeneratorLeafBlocks" not in PurePosixPath(p).name for p in warm_outputs),
            "The warm archive unexpectedly contains leaf outputs")
    bundles = [(warm_archive, warm_outputs, warm["archive_sha256"])]
    ranges = set()
    seen = dict(warm_outputs)
    for manifest_path in sorted(download.rglob("range-manifest-*.json")):
        manifest = read_json(manifest_path)
        require(manifest.get("format") == FORMAT, "Unknown range artifact manifest format")
        same_snapshot(manifest["snapshot"], source, "The downloaded range manifest")
        require(manifest.get("control_commit") == os.environ["CONTROL_COMMIT"],
                "Range artifacts were generated by a different control revision")
        first, last = manifest["first"], manifest["last"]
        require((first, last) in RANGES and (first, last) not in ranges,
                "Duplicate or unexpected range artifact")
        require(manifest_path.name == f"range-manifest-{first}-{last}.json",
                "Range manifest filename differs from its declared boundaries")
        check_range_report(manifest["range_report"], first, last, source)
        require(manifest["warm_archive_sha256"] == warm["archive_sha256"],
                "A range used different shared dependency outputs")
        archive_name = f"range-outputs-{first}-{last}.tar.gz"
        require(manifest["archive"] == archive_name, "Unexpected range archive filename")
        archive = manifest_path.with_name(archive_name)
        require(archive.is_file() and not archive.is_symlink(), "Missing regular range archive")
        require(digest(archive) == manifest["archive_sha256"], "Range archive checksum mismatch")
        require(archive.stat().st_size == manifest["archive_bytes"], "Range archive size mismatch")
        outputs = inspect_archive(archive, manifest["outputs"])
        blocks = {range_member_block(name) for name in outputs}
        require(blocks == set(range(first, last + 1)), "Range artifact does not cover its modules")
        for block in blocks:
            check_bundled_block_outputs(outputs, block)
        for name, record in outputs.items():
            require(name not in seen, f"Overlapping build artifacts: {name}")
            seen[name] = record
        ranges.add((first, last))
        bundles.append((archive, outputs, manifest["archive_sha256"]))
    require(ranges == set(RANGES), "The downloaded artifacts do not cover all 106 blocks")
    check_immutable(source)
    return source, bundles, seen


def destination(name):
    parts = safe_name(name).parts
    current = ROOT
    for part in parts:
        current = current / part
        require(not current.is_symlink(), f"Symlink in restore destination: {current}")
    return current


def restore_all(download, validate_only=False):
    source, bundles, inventory = validate_all(download)
    if not validate_only:
        for archive, outputs, checksum in bundles:
            require(digest(archive) == checksum, "An archive changed after aggregate validation")

            def visit(tar, member):
                path = destination(member.name)
                path.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as temporary:
                    temporary_path = Path(temporary.name)
                    try:
                        with tar.extractfile(member) as stream:
                            shutil.copyfileobj(stream, temporary)
                        temporary.flush()
                        require(digest(temporary_path) == outputs[member.name]["sha256"],
                                f"A restored output differs from its audited bundle: {member.name}")
                        os.chmod(temporary_path, 0o644)
                        os.utime(temporary_path, (member.mtime, member.mtime))
                        temporary_path.replace(path)
                    finally:
                        temporary_path.unlink(missing_ok=True)

            archive_members(archive, visit)
        for name, record in inventory.items():
            require(digest(ROOT / name) == record["sha256"], f"Restored output mismatch: {name}")
    check_immutable(source)
    OUT.mkdir(parents=True, exist_ok=True)
    report = {
        "format": FORMAT, "status": "validated" if validate_only else "restored",
        "snapshot": source, "control_commit": os.environ["CONTROL_COMMIT"],
        "ranges": RANGES, "output_count": len(inventory), "outputs": inventory,
    }
    write_json(OUT / "aggregate-outputs-report.json", report)
    print(f"{'Validated' if validate_only else 'Restored'} all 106 genuine leaf modules "
          f"and shared dependencies: {len(inventory)} hashed outputs", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="mode", required=True)
    packing = modes.add_parser("pack")
    packing.add_argument("--first", type=int, required=True)
    packing.add_argument("--last", type=int, required=True)
    for mode in ("restore-all", "validate-all"):
        modes.add_parser(mode).add_argument("--download-dir", type=Path, required=True)
    args = parser.parse_args()
    if args.mode == "pack":
        pack(args.first, args.last)
    else:
        restore_all(args.download_dir.resolve(), validate_only=args.mode == "validate-all")


if __name__ == "__main__":
    main()
