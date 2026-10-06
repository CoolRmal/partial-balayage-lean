#!/usr/bin/env python3
"""Build one frozen square assembly module with visible, durable diagnostics.

This is integration tooling, not the independent Palomar checker.  It neither
restores outputs nor changes source, compiler options, or verifier budgets.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import time

SOURCE = "4671737f1acc8292a5c984d00401341c8a4a5548"
ROOT = Path.cwd()
SCRIPT = Path(__file__).resolve()


def load_prepare():
    spec = importlib.util.spec_from_file_location(
        "square_assembly_prepare", SCRIPT.with_name("prepare-square-integration.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PREPARE = load_prepare()
FINAL = PREPARE.FINAL


def load_checkpoint_control():
    spec = importlib.util.spec_from_file_location(
        "square_assembly_checkpoint", SCRIPT.with_name("checkpoint-square-support.py"))
    checkpoint = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checkpoint)
    return checkpoint


def validate_checkpoint(report_dir, root):
    checkpoint = load_checkpoint_control()
    return checkpoint.validate_existing_checkpoint(report_dir, root)


def final_outputs(module):
    names = load_checkpoint_control().module_outputs(module)
    return {name: {"sha256": digest(ROOT / name), "bytes": (ROOT / name).stat().st_size}
            for name in names}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f"Nonregular evidence: {path}")
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def resource_observations():
    """Cgroup observations are measurements, not asserted resource caps."""
    result = {}
    for name in ["memory.current", "memory.peak", "memory.max", "memory.events"]:
        path = Path("/sys/fs/cgroup") / name
        try:
            result[str(path)] = path.read_text().strip()
        except OSError as exc:
            result[str(path)] = {"unavailable": type(exc).__name__}
    return result


def emit(event, **fields):
    record = {"event": event, "utc": utc_now(), **fields}
    print(json.dumps(record, sort_keys=True), flush=True)
    return record


def validate_context(report_dir, module):
    require(module in FINAL, "Unknown assembly module")
    checkpoint = validate_checkpoint(report_dir, ROOT)
    plan_path = report_dir / "integration-source-report.json"
    plan = json.loads(plan_path.read_text())
    require(plan["status"] == "applied" and plan["integration_commit"] == SOURCE,
            "Wrong applied integration source")
    require((plan["candidate"], plan["control"], plan["numerical_run"]) ==
            (PREPARE.CANDIDATE, PREPARE.CONTROL, PREPARE.RUN),
            "Wrong numerical source provenance")
    require(plan["final_modules"] == FINAL and
            plan["reviewed_final_source_sha256"] == PREPARE.FINAL_SHA256,
            "Changed frozen final sources")
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT)
            .decode().strip() == SOURCE, "Wrong working source revision")
    support_path = report_dir / "support-build-report.json"
    support = json.loads(support_path.read_text())
    preparation = plan["support_preparation"]
    require(support["status"] == "prepared" and
            support["integration_commit"] == SOURCE and
            support["restored_leaf_output_hashes_unchanged"] is True,
            "Support preparation has not completed")
    require(len(preparation["graph"]) == 717 and
            len(preparation["support_modules"]) == 367 and
            [item["module"] for item in support["modules"]] ==
            preparation["support_modules"], "Incomplete support preparation")
    require(len(plan["protected_leaf_outputs"]) == 1590,
            "Incomplete protected numerical outputs")
    checkpoint_path = report_dir / "support-checkpoint" / "support-checkpoint.json"
    require(checkpoint_path.is_file(), "Mandatory support checkpoint is missing")
    checkpoint_hash = digest(checkpoint_path)
    for previous in FINAL[:FINAL.index(module)]:
        previous_path = report_dir / "assembly-logs" / (previous + ".json")
        previous_report = json.loads(previous_path.read_text())
        require(previous_report["status"] == "built" and
                previous_report["module"] == previous and
                previous_report["integration_commit"] == SOURCE and
                previous_report["support_checkpoint_sha256"] == checkpoint_hash and
                previous_report["source_sha256"] == PREPARE.FINAL_SHA256[previous],
                "Previous assembly module has not passed with this checkpoint")
        require(previous_report["final_output_files"] == final_outputs(previous),
                "Previous assembly outputs changed")
    context = {"plan": plan, "plan_sha256": digest(plan_path),
               "completed_support_outputs": checkpoint["manifest"]["outputs"],
               "support_report_sha256": digest(support_path),
               "support_checkpoint_sha256": checkpoint_hash,
               "module": module, "integration_commit": SOURCE,
               "source_sha256": PREPARE.FINAL_SHA256[module]}
    check_sources_and_leaves(context)
    return context


def check_sources_and_leaves(context):
    plan = context["plan"]
    for module, item in plan["support_preparation"]["graph"].items():
        require(digest(ROOT / item["path"]) == item["sha256"],
                f"Changed integration source: {module}")
    for path, item in plan["protected_leaf_outputs"].items():
        require(digest(ROOT / path) == item["sha256"], f"Changed numerical output: {path}")
    for path, item in context["completed_support_outputs"].items():
        require(digest(ROOT / path) == item["sha256"], f"Changed completed support output: {path}")


class Terminated(Exception):
    pass


def stream_command(argv, log_path, resource_time, module, stage, heartbeat_seconds=30):
    """Stream merged output to the CI log and a flushed local file."""
    actual = ["/usr/bin/time", "-v", "-o", str(resource_time), *argv]
    started = time.monotonic()
    begin = emit("command-start", module=module, stage=stage, argv=actual,
                 cgroup_observations=resource_observations())
    process = None
    interrupted = False
    try:
        with Path(log_path).open("wb") as log:
            process = subprocess.Popen(actual, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ)
                next_heartbeat = time.monotonic() + heartbeat_seconds
                while selector.get_map():
                    remaining = max(0, next_heartbeat - time.monotonic())
                    for key, _ in selector.select(min(remaining, 1)):
                        data = os.read(key.fileobj.fileno(), 65536)
                        if data:
                            log.write(data)
                            log.flush()
                            sys.stdout.buffer.write(data)
                            sys.stdout.buffer.flush()
                        else:
                            selector.unregister(key.fileobj)
                    if time.monotonic() >= next_heartbeat:
                        emit("command-heartbeat", module=module, stage=stage,
                             elapsed_seconds=time.monotonic() - started,
                             cgroup_observations=resource_observations())
                        next_heartbeat = time.monotonic() + heartbeat_seconds
            returncode = process.wait()
            log.flush()
            os.fsync(log.fileno())
    except BaseException:
        interrupted = True
        raise
    finally:
        if process is not None and process.poll() is None:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        end = emit("command-end", module=module, stage=stage, argv=actual,
                   returncode=None if process is None else process.returncode,
                   interrupted=interrupted, elapsed_seconds=time.monotonic() - started,
                   cgroup_observations=resource_observations())
        write_json(Path(log_path).with_suffix(".json"), {"start": begin, "end": end})
    result = {"argv": actual, "returncode": returncode,
              "wall_seconds": time.monotonic() - started,
              "log": str(log_path), "log_sha256": digest(log_path),
              "resource_time": str(resource_time),
              "resource_time_sha256": digest(resource_time)}
    require(returncode == 0, f"{stage} failed for {module}: exit {returncode}")
    require("Exit status: 0" in Path(resource_time).read_text(),
            f"GNU time did not record success for {module}: {stage}")
    return result


def build_module(report_dir, module):
    context = validate_context(report_dir, module)
    logs = report_dir / "assembly-logs"
    logs.mkdir(exist_ok=True)
    report_path = logs / (module + ".json")
    require(not report_path.exists(), "Refusing to overwrite an assembly attempt")
    report = {key: value for key, value in context.items()
              if key not in {"plan", "completed_support_outputs"}}
    report.update({"status": "building", "commands": [], "started_utc": utc_now(),
                   "control_script_sha256": digest(SCRIPT),
                   "github_run_id": os.environ.get("GITHUB_RUN_ID"),
                   "github_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
                   "github_sha": os.environ.get("GITHUB_SHA")})
    write_json(report_path, report)
    emit("module-start", module=module, source_sha256=context["source_sha256"])
    try:
        for stage, argv in [
                ("deps", ["lake", "--no-build", "build", "+" + module + ":deps"]),
                ("build", ["lake", "build", module])]:
            result = stream_command(argv, logs / (module + "-" + stage + ".log"),
                                    logs / (module + "-" + stage + ".time"), module, stage)
            report["commands"].append(result)
            check_sources_and_leaves(context)
            require(digest(report_dir / "support-checkpoint" / "support-checkpoint.json") ==
                    context["support_checkpoint_sha256"], "Support checkpoint changed")
            write_json(report_path, report)
        report["status"] = "built"
        report["restored_leaf_output_hashes_unchanged"] = True
        report["final_output_files"] = final_outputs(module)
    except BaseException as exc:
        report["status"] = "interrupted" if isinstance(exc, Terminated) else "failed"
        report["exception"] = {"type": type(exc).__name__, "message": str(exc)}
        raise
    finally:
        report["finished_utc"] = utc_now()
        write_json(report_path, report)
        emit("module-end", module=module, status=report["status"],
             cgroup_observations=resource_observations())
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path, required=True)
    parser.add_argument("--module", choices=FINAL, required=True)
    args = parser.parse_args()

    def stop(signum, frame):
        raise Terminated(f"Observed signal {signum}")

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        build_module(args.report_dir, args.module)
    except Terminated as exc:
        emit("assembly-interrupted", module=args.module, detail=str(exc))
        return 143
    except Exception as exc:
        emit("assembly-error", module=args.module, exception=type(exc).__name__, detail=str(exc))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
