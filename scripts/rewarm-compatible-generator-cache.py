#!/usr/bin/env python3
"""Reuse an unchanged dependency cache, then produce fresh candidate warm evidence.

Default mode only inspects Git objects. ``--execute-isolated-switch`` is reserved
for an explicitly isolated CI checkout already at OLD_COMMIT. It restores the
old artifact with that revision's original driver, switches to the new immutable
revision, and runs its ordinary warm mode. No old manifest is rewritten/relabelled.
Python verifies cache compatibility and evidence provenance; it proves no Lean
statement. The final submission still needs its independent source-based check.
"""

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile

OLD_COMMIT = "1e84ddabfbf64c3f4fe29cb61a85571f5caa7543"
PUBLIC_REPOSITORY = "CoolRmal/partial-balayage-lean"
SEED_RUN = "37401878571"
SEED_MANIFEST_SHA256 = "67a0bacb542c5e8235a19743dc4e99d4e9d75ce7377179104aba424701af2c89"
SEED_ARCHIVE_SHA256 = "fb32c9ce1030c68c61ef4b8979df3c4d0997000299b5a8bdcdb9b06ba43ff951"
SEED_ARCHIVE_BYTES = 215550212
SEED_OUTPUT_COUNT = 3600
SEED_UNCOMPRESSED_BYTES = 1393147945
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "c55e6e786f49471c72fbddbec5415808896aec1e"
NAMESPACE = "PartialBalayage.Maximal.Square"
PREFIX = NAMESPACE + ".Data.GeneratorLeafBlocks"
DRIVER = "scripts/validate-generator-blocks.py"
PINS = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^(?:(?:public|meta)\s+)*import\s+(\S+)", re.MULTILINE)
OUTPUT_BASES = (".lake/build/lib/lean/", ".lake/build/ir/")
OUTPUT_SUFFIXES = (".olean.private.hash", ".olean.server.hash", ".olean.private",
                   ".olean.server", ".olean.hash", ".ilean.hash", ".ir.sig.hash",
                   ".ir.sig", ".ir.hash", ".c.hash", ".bc.hash", ".olean",
                   ".ilean", ".trace", ".ir", ".c", ".bc", ".hash")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root)


class Revision:
    """Read regular committed blobs without checking out or executing anything."""

    def __init__(self, root, commit):
        require(re.fullmatch(r"[0-9a-f]{40}", commit), "Expected a full lower-case SHA")
        require(git(root, "rev-parse", commit + "^{commit}").decode().strip() == commit,
                "Requested immutable commit is unavailable")
        self.root, self.commit, self.entries, self.cache = root, commit, {}, {}
        for item in git(root, "ls-tree", "-r", "-z", "--full-tree", commit).split(b"\0"):
            if item:
                header, name = item.split(b"\t", 1)
                mode, kind, oid = header.decode().split()
                self.entries[name.decode()] = (mode, kind, oid)
        self.reader = subprocess.Popen(["git", "cat-file", "--batch"], cwd=root,
                                       stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def close(self):
        self.reader.stdin.close()
        self.reader.stdout.close()
        require(self.reader.wait() == 0, "Git blob reader failed")

    def read(self, name):
        if name not in self.cache:
            require(name in self.entries, f"Missing committed source: {name}")
            mode, kind, oid = self.entries[name]
            require(mode in {"100644", "100755"} and kind == "blob",
                    f"Source is not a regular committed file: {name}")
            self.reader.stdin.write((oid + "\n").encode())
            self.reader.stdin.flush()
            header = self.reader.stdout.readline().decode().split()
            require(len(header) == 3 and header[:2] == [oid, "blob"],
                    f"Unexpected Git blob response for {name}")
            data = self.reader.stdout.read(int(header[2]))
            require(self.reader.stdout.read(1) == b"\n", "Truncated Git blob")
            self.cache[name] = data
        return self.cache[name]

    def text(self, name):
        return self.read(name).decode()

    def source_hashes(self):
        paths = sorted(p for p in self.entries if p.endswith(".lean") or p in (*PINS, DRIVER))
        return {p: sha(self.read(p)) for p in paths}


def shared_roots(revision):
    imports = set()
    for block in range(106):
        path = PREFIX.replace(".", "/") + f"{block}.lean"
        imports.update(IMPORT.findall(revision.text(path)))
    fast, sparse = NAMESPACE + ".GeneratorLeafFastCheck", NAMESPACE + ".GeneratorLeafSparseCheck"
    roots = [fast, NAMESPACE + ".GeneratorRadialRoots", NAMESPACE + ".GeneratorPartitionRectangles"]
    if sparse in imports:
        roots.append(sparse)
    coordinates = sorted((m for m in imports if ".Data.GeneratorCoordinates" in m),
                         key=lambda m: int(m.rsplit("GeneratorCoordinates", 1)[1]))
    require(imports <= set(roots + coordinates), "Unexpected candidate dependency root")
    require(set(roots[1:3]) <= imports and bool({fast, sparse} & imports),
            "Missing candidate dependency root")
    return roots + coordinates


def shared_closure(revision, roots):
    pending, files, external = list(roots), {}, set()
    while pending:
        module = pending.pop()
        path = module.replace(".", "/") + ".lean"
        if path in files:
            continue
        if path not in revision.entries:
            require(not module.startswith(("PartialBalayage.", "CenteredMaximal.")),
                    f"Missing local transitive dependency: {module}")
            external.add(module)
            continue
        require(not module.startswith(PREFIX), "Numerical leaf in shared dependency closure")
        files[path] = sha(revision.read(path))
        pending.extend(IMPORT.findall(revision.text(path)))
    return dict(sorted(files.items())), sorted(external)


def check_pin_values(revision):
    require(revision.text("lean-toolchain").strip() == TOOLCHAIN, "Unexpected Lean toolchain")
    packages = json.loads(revision.text("lake-manifest.json"))["packages"]
    require(next(p["rev"] for p in packages if p["name"] == "mathlib") == MATHLIB,
            "Unexpected mathlib manifest pin")
    require(f'rev = "{MATHLIB}"' in revision.text("lakefile.toml"), "Unexpected lakefile pin")
    assignments = {}
    for node in ast.parse(revision.text(DRIVER)).body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
            if (isinstance(target, ast.Name) and
                    target.id in {"TOOLCHAIN", "LEAN_COMMIT", "MATHLIB"}):
                assignments[target.id] = ast.literal_eval(node.value)
    require(assignments == {"TOOLCHAIN": TOOLCHAIN, "LEAN_COMMIT": LEAN_COMMIT, "MATHLIB": MATHLIB},
            "Driver runtime pins differ")


def compare_shared(old, new, expected_sources=240):
    check_pin_values(old)
    check_pin_values(new)
    old_roots, new_roots = shared_roots(old), shared_roots(new)
    require(old_roots == new_roots, "Shared dependency root set/order changed")
    old_files, old_external = shared_closure(old, old_roots)
    new_files, new_external = shared_closure(new, new_roots)
    require(len(old_files) == expected_sources, "Unexpected shared-source count")
    require(old_files == new_files, "Shared transitive source contents or closure changed")
    require(old_external == new_external, "External transitive import set changed")
    require({p: sha(old.read(p)) for p in PINS} == {p: sha(new.read(p)) for p in PINS},
            "Dependency pins or Lake compiler/options configuration changed")
    require(("lakefile.lean" in old.entries) == ("lakefile.lean" in new.entries),
            "Alternative Lake configuration presence changed")
    if "lakefile.lean" in old.entries:
        require(old.read("lakefile.lean") == new.read("lakefile.lean"),
                "Alternative Lake configuration changed")
    return {"old_commit": old.commit, "new_commit": new.commit,
            "shared_roots": old_roots, "shared_source_count": len(old_files),
            "shared_source_hashes": old_files, "external_imports": old_external,
            "pin_hashes": {p: sha(old.read(p)) for p in PINS}}


def expected_snapshot(revision):
    return {"commit": revision.commit, "toolchain": TOOLCHAIN, "lean_commit": LEAN_COMMIT,
            "mathlib": MATHLIB, "source_hashes": revision.source_hashes()}


def check_snapshot(actual, expected, description):
    for key, value in expected.items():
        require(actual.get(key) == value, f"{description} differs in {key}")


def expected_audits(revision, roots):
    names = {NAMESPACE + ".generatorRadialRoots_valid"}
    require(NAMESPACE + ".GeneratorLeafSparseCheck" in roots, "Missing sparse evaluator")
    names.update(NAMESPACE + "." + n for n in (
        "sparseScaleInterval_eq", "sparseProduct_eq", "sparseGeneratorTensorIntervals_eq",
        "sparseGeneratorApproximationIntervals_eq", "sparseGeneratorApproximationError_eq",
        "sparseGeneratorCombinedIntervals_eq",
        "GeneratorLeafData.sparseLowerBound_eq_fastLowerBound",
        "GeneratorLeafData.sparseLowerBound_eq_lowerBound",
        "GeneratorLeafData.numericalValid_of_sparse"))
    for module in roots:
        if ".Data.GeneratorCoordinates" in module:
            names.update(NAMESPACE + "." + name for name in re.findall(
                r"theorem\s+(generatorCoordinates\d+_valid)",
                revision.text(module.replace(".", "/") + ".lean")))
    require(len(names) == 99, "Unexpected warm audit endpoint set")
    return names


def check_report(report, expected, roots, endpoints):
    require(report.get("status") == "pass", "Fresh ordinary warm report is not a pass")
    check_snapshot(report.get("snapshot", {}), expected, "Fresh warm report snapshot")
    require([m.get("module") for m in report.get("modules", [])] == roots,
            "Fresh warm report is missing or reorders required module builds")
    axioms = report.get("audit", {}).get("axioms", {})
    require(set(axioms) == endpoints, "Fresh warm report lacks all 99 actual imported audits")
    for name, basis in axioms.items():
        require(set(basis) == PERMITTED, f"Unexpected axiom basis: {name}")


def safe_output(name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and "\\" not in name,
            "Unsafe warm archive path")
    require(str(path) == name and name.startswith(OUTPUT_BASES), "Unexpected warm archive path")
    require(name.endswith(OUTPUT_SUFFIXES), "Unexpected warm archive output suffix")


def safe_archive_member(member):
    safe_output(member.name)
    require(member.isfile(), "Nonregular or linked warm archive member")


def check_archive(archive, manifest):
    require(file_digest(archive) == manifest.get("archive_sha256"),
            "Warm archive checksum mismatch")
    require(archive.stat().st_size == manifest.get("archive_bytes"), "Warm archive size mismatch")
    count, size, seen = 0, 0, set()
    proc = subprocess.Popen(["zstd", "--decompress", "--stdout", str(archive)],
                            stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as contents:
            for member in contents:
                safe_archive_member(member)
                require(member.name not in seen, "Duplicate warm archive member")
                seen.add(member.name)
                count += 1
                size += member.size
        # Drain tar padding before waiting, rather than terminating a valid decoder.
        while proc.stdout.read(1024 * 1024):
            pass
    finally:
        proc.stdout.close()
        if proc.poll() is None:
            # A failed archive validation may leave the decoder blocked on the pipe.
            if sys.exc_info()[0] is not None:
                proc.terminate()
        code = proc.wait()
    require(code == 0, "Warm archive decompression failed")
    require(count == manifest.get("artifact_output_count"), "Warm output count mismatch")
    require(size == manifest.get("uncompressed_bytes"), "Warm uncompressed-size mismatch")


def clean_checkout_at(root, commit, revision):
    require(git(root, "rev-parse", "HEAD").decode().strip() == commit, "Checkout is at wrong HEAD")
    require(not git(root, "status", "--porcelain", "--untracked-files=no"),
            "Tracked checkout is dirty")
    require((root / DRIVER).is_file() and not (root / DRIVER).is_symlink(), "Nonregular driver")
    require(sha((root / DRIVER).read_bytes()) == sha(revision.read(DRIVER)),
            "Driver differs from commit")


def check_repository(root):
    origin = git(root, "remote", "get-url", "origin").decode().strip()
    require(origin in {f"https://github.com/{PUBLIC_REPOSITORY}.git",
                       f"https://github.com/{PUBLIC_REPOSITORY}",
                       f"git@github.com:{PUBLIC_REPOSITORY}.git"}, "Unexpected public repository")


def check_control_checkout(root):
    script = Path(__file__).resolve()
    control = Path(git(script.parent, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    require(control != root, "Guard must run from a separate dispatcher/control checkout")
    check_repository(control)
    expected = os.environ.get("CONTROL_COMMIT", "")
    require(re.fullmatch(r"[0-9a-f]{40}", expected), "Missing full CONTROL_COMMIT")
    require(git(control, "rev-parse", "HEAD").decode().strip() == expected,
            "Control checkout differs from CONTROL_COMMIT")
    relative = script.relative_to(control).as_posix()
    require(sha(git(control, "show", f"{expected}:{relative}")) == file_digest(script),
            "Running guard differs from its committed control source")
    require(not git(control, "diff", "--name-only", "HEAD", "--", relative),
            "Running guard has uncommitted changes")
    return expected


def check_seed_identity(manifest_bytes, manifest):
    require(sha(manifest_bytes) == SEED_MANIFEST_SHA256, "Seed manifest differs from verified run")
    require(manifest.get("archive_sha256") == SEED_ARCHIVE_SHA256,
            "Seed archive identity differs from verified run")
    require(manifest.get("archive_bytes") == SEED_ARCHIVE_BYTES, "Seed archive byte count differs")
    require(manifest.get("artifact_output_count") == SEED_OUTPUT_COUNT, "Seed output count differs")
    require(manifest.get("uncompressed_bytes") == SEED_UNCOMPRESSED_BYTES,
            "Seed uncompressed byte count differs")


def build_output_identity(root):
    paths = []
    for base in OUTPUT_BASES:
        directory = root / base
        if directory.exists():
            paths.extend(p for p in directory.rglob("*") if p.is_file())
    require(paths, "Restored .lake build cache is empty")
    require(all(not p.is_symlink() for p in paths), "Linked file in restored .lake cache")
    return {str(p.relative_to(root)): file_digest(p) for p in sorted(paths)}


def execute(root, old, new, args, compatibility):
    require(old.commit != new.commit, "New candidate must differ from old candidate")
    check_repository(root)
    control_commit = check_control_checkout(root)
    require(os.environ.get("GITHUB_REPOSITORY", PUBLIC_REPOSITORY) == PUBLIC_REPOSITORY,
            "Workflow repository differs from the expected public repository")
    clean_checkout_at(root, old.commit, old)
    download = args.runner_temp / "square-numerical-download"
    manifest_path, archive = download / "warm-manifest.json", download / "warm-outputs.tar.zst"
    old_bytes = manifest_path.read_bytes()
    manifest = json.loads(old_bytes)
    check_seed_identity(old_bytes, manifest)
    check_snapshot(manifest, expected_snapshot(old), "Original downloaded manifest")
    check_archive(archive, manifest)
    env = dict(os.environ, RUNNER_TEMP=str(args.runner_temp), NUMERICAL_COMMIT=old.commit)
    subprocess.run([sys.executable, DRIVER, "restore"], cwd=root, env=env, check=True)
    clean_checkout_at(root, old.commit, old)
    restored_outputs = build_output_identity(root)
    require(manifest_path.read_bytes() == old_bytes,
            "Original manifest was modified during restore")
    subprocess.run(["git", "switch", "--detach", new.commit], cwd=root, check=True)
    clean_checkout_at(root, new.commit, new)
    require(build_output_identity(root) == restored_outputs,
            "Restored .lake outputs changed during the isolated source switch")
    # Recheck the full shared compatibility after switching; no manifest is relabelled.
    require(compare_shared(old, new, args.expected_sources) == compatibility,
            "Compatibility facts changed before fresh warm mode")
    env["NUMERICAL_COMMIT"] = new.commit
    subprocess.run([sys.executable, DRIVER, "warm"], cwd=root, env=env, check=True)
    clean_checkout_at(root, new.commit, new)
    out = args.runner_temp / "square-numerical"
    fresh = json.loads((out / "warm-manifest.json").read_text())
    expected = expected_snapshot(new)
    check_snapshot(fresh, expected, "Genuine newly generated warm manifest")
    check_report(json.loads((out / "warm-report.json").read_text()), expected,
                 compatibility["shared_roots"], expected_audits(new, compatibility["shared_roots"]))
    check_archive(out / "warm-outputs.tar.zst", fresh)
    require(manifest_path.read_bytes() == old_bytes, "Original downloaded manifest was relabelled")
    compatibility.update(status="fresh-warm-pass", imported_audit_count=99,
                         seed_run=SEED_RUN, repository=PUBLIC_REPOSITORY,
                         control_commit=control_commit,
                         original_manifest_sha256=sha(old_bytes),
                         fresh_manifest_sha256=file_digest(out / "warm-manifest.json"),
                         fresh_archive_sha256=fresh["archive_sha256"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old-commit", default=OLD_COMMIT)
    parser.add_argument("--new-commit", required=True)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--runner-temp", type=Path,
                        default=Path(os.environ.get("RUNNER_TEMP", "/tmp")))
    parser.add_argument("--expected-sources", type=int, default=240)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--execute-isolated-switch", action="store_true",
                        help="Restore/switch/rewarm an explicitly isolated checkout; invokes Lean")
    args = parser.parse_args()
    require(args.old_commit == OLD_COMMIT, "Only the fixed verified seed commit is supported")
    args.root, args.runner_temp = args.root.resolve(), args.runner_temp.resolve()
    old, new = Revision(args.root, args.old_commit), None
    try:
        new = Revision(args.root, args.new_commit)
        compatibility = compare_shared(old, new, args.expected_sources)
        expected_audits(new, compatibility["shared_roots"])
        compatibility["status"] = "compatible-sources-only"
        if args.execute_isolated_switch:
            execute(args.root, old, new, args, compatibility)
        if args.report:
            args.report.write_text(json.dumps(compatibility, indent=2, sort_keys=True) + "\n")
        print(json.dumps({k: compatibility[k] for k in (
            "status", "old_commit", "new_commit", "shared_source_count")}, indent=2))
    finally:
        old.close()
        if new is not None:
            new.close()


if __name__ == "__main__":
    main()
