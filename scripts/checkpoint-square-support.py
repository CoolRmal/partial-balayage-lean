#!/usr/bin/env python3
"""Package completed support outputs before square assembly, without running Lean.

Run from the isolated mathematical checkout using the committed control checkout.
This checkpoint preserves completed build work; it is not final theorem acceptance.
There is deliberately no restoration or proof-build mode.
"""

import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tarfile
import tempfile

FORMAT = "square-support-checkpoint-v1"
SOURCE = "4671737f1acc8292a5c984d00401341c8a4a5548"
CANDIDATE = "dde634e918bcbba00881018b205dea4172d2ee5f"
CONTROL = "243a5bd4f80c9517e7c9f834e85c5154eeb8e9a9"
NUMERICAL_RUN = 37409981058
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "c55e6e786f49471c72fbddbec5415808896aec1e"
PREFIX = "PartialBalayage.Maximal.Square.Data.GeneratorLeafBlocks"
PIN_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
LIB_SUFFIXES = (
    ".olean", ".olean.private", ".olean.server", ".ilean", ".trace",
    ".olean.hash", ".olean.private.hash", ".olean.server.hash", ".ilean.hash",
    ".ir", ".ir.hash", ".ir.sig", ".ir.sig.hash",
)
IR_SUFFIXES = (".c", ".c.hash")
MODULE = re.compile(r"(?:PartialBalayage|CenteredMaximal)(?:\.[A-Za-z_][A-Za-z_0-9]*)+")
SHA = re.compile(r"[0-9a-f]{64}")
sys.dont_write_bytecode = True


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, f"Duplicate JSON key: {key}")
        value[key] = item
    return value


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


def regular(root, name):
    relative = PurePosixPath(name)
    require(not relative.is_absolute() and ".." not in relative.parts and "\\" not in name,
            f"Unsafe path: {name}")
    require(str(relative) == name and name not in ("", "."), f"Noncanonical path: {name}")
    current = root
    for part in relative.parts:
        current = current / part
        require(not current.is_symlink(), f"Symlink path: {name}")
    require(stat.S_ISREG(current.stat().st_mode), f"Nonregular file: {name}")
    return current


def command(root, *args):
    return subprocess.check_output(["git", *args], cwd=root)


def module_outputs(module):
    require(MODULE.fullmatch(module), f"Unsafe project module: {module}")
    stem = module.replace(".", "/")
    return [".lake/build/lib/lean/" + stem + suffix for suffix in LIB_SUFFIXES] + [
        ".lake/build/ir/" + stem + suffix for suffix in IR_SUFFIXES]


def runtime_context(root, control_root, environment):
    require(environment.get("GITHUB_REPOSITORY") == "CoolRmal/partial-balayage-lean",
            "Unexpected repository identity")
    head = environment.get("GITHUB_SHA", "")
    require(re.fullmatch(r"[0-9a-f]{40}", head), "Missing exact workflow control SHA")
    for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"):
        require(re.fullmatch(r"[1-9][0-9]*", environment.get(key, "")),
                f"Missing actual positive {key}")
    require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9-]*", environment.get("GITHUB_JOB", "")),
            "Missing actual job identity")
    require(environment.get("NUMERICAL_COMMIT") == CANDIDATE and
            environment.get("CONTROL_COMMIT") == CONTROL and
            environment.get("NUMERICAL_RUN") == str(NUMERICAL_RUN), "Numerical identity changed")
    require(command(root, "rev-parse", "HEAD").decode().strip() == SOURCE,
            "Outer checkout is not the fixed integration source")
    require(command(control_root, "rev-parse", "HEAD").decode().strip() == head,
            "Control checkout differs from GITHUB_SHA")
    script_hashes = {}
    for name in ("checkpoint-square-support.py", "prepare-square-integration.py"):
        relative = "scripts/" + name
        actual = regular(control_root, relative)
        committed = command(control_root, "show", f"{head}:{relative}")
        require(sha(committed) == digest(actual), f"Uncommitted control script: {name}")
        script_hashes[relative] = sha(committed)
    pin_hashes = {}
    for name in PIN_FILES:
        actual = regular(root, name)
        source = command(root, "show", f"{SOURCE}:{name}")
        require(source == command(root, "show", f"{CANDIDATE}:{name}"),
                f"Integration changed a dependency pin: {name}")
        require(digest(actual) == sha(source), f"Working dependency pin changed: {name}")
        pin_hashes[name] = sha(source)
    require((root / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Wrong toolchain")
    packages = read_json(root / "lake-manifest.json")["packages"]
    require([p["rev"] for p in packages if p["name"] == "mathlib"] == [MATHLIB],
            "Wrong mathlib manifest pin")
    require(f'rev = "{MATHLIB}"' in (root / "lakefile.toml").read_text(), "Wrong lakefile pin")
    require(command(root, "-C", ".lake/packages/mathlib", "rev-parse", "HEAD")
            .decode().strip() == MATHLIB, "Installed mathlib differs from the pin")
    command(root, "-C", ".lake/packages/mathlib", "diff", "--exit-code", "HEAD", "--")
    return {"repository": environment["GITHUB_REPOSITORY"], "source_commit": SOURCE,
            "workflow_control_commit": head, "run_id": int(environment["GITHUB_RUN_ID"]),
            "run_attempt": int(environment["GITHUB_RUN_ATTEMPT"]),
            "job": environment.get("GITHUB_JOB", ""), "candidate": CANDIDATE,
            "numeric_control_commit": CONTROL, "numerical_run": NUMERICAL_RUN,
            "toolchain": TOOLCHAIN, "lean_commit": LEAN_COMMIT, "mathlib": MATHLIB,
            "pin_file_sha256": pin_hashes, "control_script_sha256": script_hashes}


def expected_plan(root, control_root):
    path = control_root / "scripts/prepare-square-integration.py"
    spec = importlib.util.spec_from_file_location("square_support_preparation", path)
    control = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(control)
    control.ROOT = root
    require((control.CANDIDATE, control.CONTROL, control.RUN) ==
            (CANDIDATE, CONTROL, NUMERICAL_RUN), "Unexpected preparation constants")
    numeric = control.closure()
    paths = set(command(root, "ls-tree", "-r", "--name-only", SOURCE).decode().splitlines())
    finals = control.reviewed_final_sources(SOURCE, paths)
    preparation = control.support_plan(SOURCE, paths, numeric)
    require(len(numeric) == 346 and len(preparation["support_modules"]) == 367 and
            len(preparation["graph"]) == 717 and len(finals) == 4, "Wrong exact module split")
    return {"closure": numeric, "support_preparation": preparation,
            "reviewed_final_source_sha256": finals, "final_modules": control.FINAL}


def validate_reports(root, report_dir, expected, context):
    names = ("integration-source-report.json", "support-build-report.json",
             "aggregate-outputs-report.json")
    reports = {name: read_json(regular(report_dir, name)) for name in names}
    plan, support, aggregate = (reports[name] for name in names)
    require(plan.get("status") == "applied" and plan.get("integration_commit") == SOURCE and
            plan.get("candidate") == CANDIDATE and plan.get("control") == CONTROL and
            plan.get("numerical_run") == NUMERICAL_RUN, "Wrong integration source report")
    for key, value in expected.items():
        require(plan.get(key) == value, f"Source report differs in {key}")
    graph = expected["support_preparation"]["graph"]
    numeric = expected["closure"]
    modules = expected["support_preparation"]["support_modules"]
    finals = expected["final_modules"]
    require(len(graph) == 717 and len(numeric) == 346 and len(modules) == 367 and
            len(set(modules)) == 367 and len(finals) == 4, "Incomplete exact source graph")
    require(set(graph) == set(numeric) | set(modules) | set(finals), "Graph partition differs")
    for module, item in graph.items():
        require(MODULE.fullmatch(module) and item["path"] == module.replace(".", "/") + ".lean",
                f"Unsafe source graph path: {module}")
        require(digest(regular(root, item["path"])) == item["sha256"],
                f"Source changed: {module}")
    require(support.get("status") == "prepared" and support.get("integration_commit") == SOURCE
            and support.get("restored_leaf_output_hashes_unchanged") is True
            and support.get("protected_leaf_outputs") == 1590, "Support is not fully prepared")
    records = support.get("modules", [])
    require([r.get("module") for r in records] == modules, "Incomplete/duplicate support records")
    log_hashes = {}
    for record in records:
        module = record["module"]
        require(record.get("source_sha256") == graph[module]["sha256"],
                f"Completed support record has changed source: {module}")
        seconds = record.get("wall_seconds")
        require(isinstance(seconds, (int, float)) and not isinstance(seconds, bool) and
                math.isfinite(seconds) and seconds >= 0, f"Invalid actual duration: {module}")
        for key, suffix in (("build_log", "-build.log"), ("resource_time", ".time")):
            name = "support-logs/" + module + suffix
            file = regular(report_dir, name)
            require(Path(record.get(key, "")).absolute() == file.absolute(),
                    f"Support record points outside its actual log: {module}")
            log_hashes[name] = {"sha256": digest(file), "bytes": file.stat().st_size}
        dep = regular(report_dir, "support-logs/" + module + "-deps.log")
        log_hashes[dep.relative_to(report_dir).as_posix()] = {
            "sha256": digest(dep), "bytes": dep.stat().st_size}
        time_text = regular(report_dir, "support-logs/" + module + ".time").read_text()
        timed = re.findall(r'^\s*Command being timed:\s*"([^"\n]*)"\s*$',
                           time_text, re.MULTILINE)
        require(timed == ["lake build " + module], f"Wrong actual support command: {module}")
        require(re.findall(r"^\s*Exit status:\s*(\d+)\s*$", time_text, re.MULTILINE) == ["0"],
                f"Support build did not record an actual successful exit: {module}")
        for suffix in ("-build.log", "-deps.log"):
            require(not re.search(r"\berror:", regular(report_dir,
                    "support-logs/" + module + suffix).read_text()),
                    f"Support log contains a compiler/dependency error: {module}")
        require(record.get("return_code", 0) == 0, f"Failed support record: {module}")
    snapshot = aggregate.get("snapshot", {})
    require(aggregate.get("status") == "restored" and aggregate.get("control_commit") == CONTROL
            and aggregate.get("output_count") == 5190 and snapshot.get("commit") == CANDIDATE,
            "Wrong restored numerical output report")
    for key in ("toolchain", "lean_commit", "mathlib"):
        require(snapshot.get(key) == context[key], f"Restored numerical pin differs: {key}")
    for name, value in context["pin_file_sha256"].items():
        require(snapshot.get("source_hashes", {}).get(name) == value, f"Pin report differs: {name}")
        require(digest(regular(root, name)) == value, f"Working pin changed: {name}")
    numeric_names = {name for module in numeric for name in module_outputs(module)}
    require(set(aggregate.get("outputs", {})) == numeric_names, "Numeric output set differs")
    leaf_names = {name for block in range(106) for name in module_outputs(PREFIX + str(block))}
    protected = {name: aggregate["outputs"][name] for name in leaf_names}
    require(len(protected) == 1590 and plan.get("protected_leaf_outputs") == protected,
            "Protected leaf inventory differs")
    for name, value in aggregate["outputs"].items():
        file = regular(root, name)
        require(file.stat().st_size == value["bytes"] and digest(file) == value["sha256"],
                f"Restored numerical output changed: {name}")
    source_run = read_json(regular(report_dir.parent, "source-run.json"))
    require(source_run.get("id") == NUMERICAL_RUN and source_run.get("head_sha") == CONTROL
            and source_run.get("status") == "completed"
            and source_run.get("conclusion") == "success"
            and source_run.get("path") == ".github/workflows/square-numerical-checks.yml"
            and source_run.get("event") == "workflow_dispatch", "Numerical run is not actual PASS")
    report_hashes = {name: digest(regular(report_dir, name)) for name in names}
    report_hashes["source-run.json"] = digest(regular(report_dir.parent, "source-run.json"))
    return {"source_graph": graph,
            "reviewed_final_source_sha256": expected["reviewed_final_source_sha256"],
            "numeric_modules": sorted(numeric), "support_modules": modules,
            "excluded_final_modules": finals, "report_sha256": report_hashes,
            "support_log_files": log_hashes, "protected_leaf_outputs": protected}


def inventory(root, checked):
    modules = checked["numeric_modules"] + checked["support_modules"]
    require(len(modules) == 713 and len(set(modules)) == 713, "Wrong completed module count")
    require(not (set(modules) & set(checked["excluded_final_modules"])), "Final module included")
    outputs = {}
    for module in modules:
        names = module_outputs(module)
        actual_trace = read_json(regular(root, names[4]))
        trace = actual_trace.get("outputs", {})
        require(trace.get("m") is True and len(trace.get("o", [])) == 3 and
                trace.get("r") and trace.get("rs") and trace.get("c") and trace.get("i"),
                f"Incomplete actual module output trace: {module}")
        labels = [entry[0] for entry in actual_trace.get("inputs", [])]
        require("Lean 4.35.0, commit " + LEAN_COMMIT in labels and
                "Module.name: " + module in labels, f"Wrong actual compiler/module trace: {module}")
        for name in names:
            file = regular(root, name)
            require(name not in outputs, f"Duplicate enumerated output: {name}")
            outputs[name] = {"sha256": digest(file), "bytes": file.stat().st_size}
    require(len(outputs) == 10695, "Wrong exact output count")
    return outputs


def inspect_tar(stream, expected):
    found = {}
    with tarfile.open(fileobj=stream, mode="r|", ignore_zeros=True) as archive:
        for member in archive:
            require(member.name in expected, f"Unexpected/unsafe archive member: {member.name}")
            require(member.type in (tarfile.REGTYPE, tarfile.AREGTYPE),
                    f"Nonregular archive member: {member.name}")
            require(member.name not in found, f"Duplicate archive member: {member.name}")
            require(member.size == expected[member.name]["bytes"], f"Archive size: {member.name}")
            content = archive.extractfile(member)
            h = hashlib.sha256()
            for chunk in iter(lambda: content.read(1024 * 1024), b""):
                h.update(chunk)
            found[member.name] = {"sha256": h.hexdigest(), "bytes": member.size}
    require(found == expected, "Missing or changed archive members")


def inspect_archive(path, expected):
    with tempfile.TemporaryFile() as errors:
        process = subprocess.Popen(["zstd", "--quiet", "--decompress", "--stdout", str(path)],
                                   stdout=subprocess.PIPE, stderr=errors)
        try:
            inspect_tar(process.stdout, expected)
            require(process.wait() == 0, "Checkpoint decompression failed")
        finally:
            process.stdout.close()
            if process.poll() is None:
                process.terminate()
            process.wait()


def pack(root, control_root, report_dir, environment):
    context = runtime_context(root, control_root, environment)
    expected = expected_plan(root, control_root)
    checked = validate_reports(root, report_dir, expected, context)
    outputs = inventory(root, checked)
    destination = report_dir / "support-checkpoint"
    require(not destination.exists(), "Checkpoint destination already exists")
    destination.mkdir()
    archive = destination / "support-outputs.tar.zst"
    temporary = destination / "support-outputs.tar.zst.part"
    with tempfile.TemporaryFile() as errors:
        process = subprocess.Popen(["zstd", "--quiet", "--threads=1", "-3", "-o", str(temporary)],
                                   stdin=subprocess.PIPE, stderr=errors)
        try:
            with tarfile.open(fileobj=process.stdin, mode="w|", format=tarfile.USTAR_FORMAT) as tar:
                for name, value in sorted(outputs.items()):
                    path = regular(root, name)
                    require(digest(path) == value["sha256"],
                            f"Output changed before packing: {name}")
                    info = tarfile.TarInfo(name)
                    info.size, info.mode = value["bytes"], 0o644
                    with path.open("rb") as stream:
                        tar.addfile(info, stream)
                    require(digest(path) == value["sha256"],
                            f"Output changed during packing: {name}")
            process.stdin.close()
            require(process.wait() == 0, "Checkpoint compression failed")
        finally:
            if not process.stdin.closed:
                process.stdin.close()
            if process.poll() is None:
                process.terminate()
            process.wait()
    inspect_archive(temporary, outputs)
    require(runtime_context(root, control_root, environment) == context,
            "Runtime source/pin/control identity changed during packing")
    require(validate_reports(root, report_dir, expected, context) == checked,
            "Source or completed support evidence changed during packing")
    require(inventory(root, checked) == outputs, "Completed outputs changed during packing")
    temporary.replace(archive)
    manifest = {"format": FORMAT, "status": "completed-support-checkpoint",
                "acceptance": (
                    "support cache only; assembly and final verification/registry pending"),
                "context": context, **checked, "completed_module_count": 713,
                "numeric_module_count": 346, "support_module_count": 367,
                "source_module_count": 717, "excluded_final_count": 4,
                "output_count": len(outputs), "outputs_per_module": 15, "outputs": outputs,
                "archive": archive.name, "archive_sha256": digest(archive),
                "archive_bytes": archive.stat().st_size}
    path = destination / "support-checkpoint.json"
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(f"Completed support checkpoint: 713 modules, 10695 outputs, {path}", flush=True)
    return manifest


def validate_existing_checkpoint(report_dir, root):
    """Read-only preassembly guard; never decompress, restore, build or rearchive."""
    root, report_dir = Path(root).resolve(), Path(report_dir).absolute()
    control_root = Path(__file__).resolve().parent.parent
    path = regular(report_dir, "support-checkpoint/support-checkpoint.json")
    manifest = read_json(path)
    context = runtime_context(root, control_root, dict(os.environ))
    expected = expected_plan(root, control_root)
    checked = validate_reports(root, report_dir, expected, context)
    require(manifest.get("format") == FORMAT and
            manifest.get("status") == "completed-support-checkpoint",
            "Wrong checkpoint format/status")
    require(manifest.get("context") == context, "Checkpoint run/source/pin context changed")
    for key, value in checked.items():
        require(manifest.get(key) == value, f"Checkpoint completed evidence changed: {key}")
    counts = {"completed_module_count": 713, "numeric_module_count": 346,
              "support_module_count": 367, "source_module_count": 717,
              "excluded_final_count": 4, "output_count": 10695, "outputs_per_module": 15}
    require(all(manifest.get(key) == value for key, value in counts.items()),
            "Checkpoint exact counts changed")
    require(manifest.get("outputs") == inventory(root, checked),
            "Completed output inventory changed since checkpoint")
    require(manifest.get("archive") == "support-outputs.tar.zst" and
            SHA.fullmatch(manifest.get("archive_sha256", "")),
            "Unsafe checkpoint archive reference")
    archive = regular(report_dir, "support-checkpoint/support-outputs.tar.zst")
    require(archive.stat().st_size == manifest.get("archive_bytes"),
            "Checkpoint archive size changed")
    require(digest(archive) == manifest["archive_sha256"], "Checkpoint archive hash changed")
    return {"manifest": manifest, "manifest_sha256": digest(path)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["pack"])
    parser.add_argument("--report-dir", type=Path, required=True)
    args = parser.parse_args()
    pack(Path.cwd().resolve(), Path(__file__).resolve().parent.parent,
         args.report_dir.absolute(), dict(os.environ))


if __name__ == "__main__":
    main()
