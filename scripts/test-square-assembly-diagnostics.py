#!/usr/bin/env python3
"""Exercise the actual assembly diagnostic helper with synthetic evidence and processes.

No compiler, proof command, exporter, restoration, or source transition is run.
The support-checkpoint validator is a separately tested seam; context tests
explicitly replace it with synthetic accepted evidence or rejection.
"""
import argparse
from contextlib import ExitStack
import copy
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import types
from unittest.mock import patch


def load_helper(path):
    spec = importlib.util.spec_from_file_location("tested_square_diagnostics", path)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    return helper


def sha(data):
    return hashlib.sha256(data).hexdigest()


def json_file(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value) + "\n")


class ContextFixture:
    """Synthetic source/output inventory, never Lean evidence."""
    def __init__(self, root, helper):
        self.root, self.helper = root, helper
        self.report = root / "reports"
        self.report.mkdir()
        self.checkpoint = self.report / "support-checkpoint/support-checkpoint.json"
        self.source = root / "synthetic-source.txt"
        self.source.write_bytes(b"synthetic shared source")
        self.output = root / "synthetic-completed-support.bin"
        self.output.write_bytes(b"synthetic completed support output")
        self.final_hashes = {}
        self.final_output_maps = {}
        graph = {}
        for number, module in enumerate(helper.FINAL):
            path = root / (module.replace(".", "/") + ".fixture")
            path.parent.mkdir(parents=True, exist_ok=True)
            data = ("synthetic final source " + module).encode()
            path.write_bytes(data)
            self.final_hashes[module] = sha(data)
            graph[module] = {"path": str(path.relative_to(root)), "sha256": sha(data)}
            self.final_output_maps[module] = {}
            for index in range(15):
                output = root / f"synthetic-final-{number}-{index}.bin"
                output.write_bytes(b"synthetic final output")
                self.final_output_maps[module][output.name] = {
                    "sha256": sha(output.read_bytes()), "bytes": output.stat().st_size}
        self.final_path = root / graph[helper.FINAL[0]]["path"]
        self.final_data = self.final_path.read_bytes()
        support_modules = [f"Synthetic.Support{i}" for i in range(367)]
        for module in support_modules + [f"Synthetic.Shared{i}" for i in range(346)]:
            graph[module] = {"path": self.source.name, "sha256": sha(self.source.read_bytes())}
        assert len(graph) == 717
        leaf_dir = root / "synthetic-leaves"
        leaf_dir.mkdir()
        leaves = {}
        for i in range(1590):
            path = leaf_dir / f"output-{i}.bin"
            path.write_bytes(b"synthetic numerical output")
            leaves[str(path.relative_to(root))] = {"sha256": sha(path.read_bytes())}
        self.leaf = leaf_dir / "output-0.bin"
        self.plan = {"status": "applied", "integration_commit": helper.SOURCE,
                     "candidate": helper.PREPARE.CANDIDATE,
                     "control": helper.PREPARE.CONTROL, "numerical_run": helper.PREPARE.RUN,
                     "final_modules": list(helper.FINAL),
                     "reviewed_final_source_sha256": dict(self.final_hashes),
                     "support_preparation": {"graph": graph, "support_modules": support_modules},
                     "protected_leaf_outputs": leaves}
        self.support = {"status": "prepared", "integration_commit": helper.SOURCE,
                        "restored_leaf_output_hashes_unchanged": True,
                        "modules": [{"module": m} for m in support_modules]}
        self.checkpoint_evidence = {"manifest": {"outputs": {
            self.output.name: {"sha256": sha(self.output.read_bytes()),
                               "bytes": self.output.stat().st_size}}}}
        self.reset()

    def reset(self):
        self.source.write_bytes(b"synthetic shared source")
        self.output.write_bytes(b"synthetic completed support output")
        if self.leaf.is_symlink():
            self.leaf.unlink()
        self.leaf.write_bytes(b"synthetic numerical output")
        if self.final_path.is_symlink():
            self.final_path.unlink()
        self.final_path.write_bytes(self.final_data)
        if self.checkpoint.is_symlink():
            self.checkpoint.unlink()
        json_file(self.checkpoint, {"synthetic_checkpoint_only": True})
        self.write(self.plan, self.support)
        for module in self.helper.FINAL:
            json_file(self.previous_path(module), {"status": "built", "module": module,
                "integration_commit": self.helper.SOURCE,
                "support_checkpoint_sha256": sha(self.checkpoint.read_bytes()),
                "source_sha256": self.final_hashes[module],
                "final_output_files": self.final_output_maps[module]})

    def previous_path(self, module):
        return self.report / "assembly-logs" / (module + ".json")

    def write(self, plan, support):
        json_file(self.report / "integration-source-report.json", plan)
        json_file(self.report / "support-build-report.json", support)

    def patches(self, stack, head=None, checkpoint_error=False):
        stack.enter_context(patch.object(self.helper, "ROOT", self.root))
        stack.enter_context(patch.object(self.helper.PREPARE, "FINAL_SHA256", self.final_hashes))
        stack.enter_context(patch.object(self.helper, "final_outputs",
            side_effect=lambda module: copy.deepcopy(self.final_output_maps[module])))
        checkpoint = stack.enter_context(patch.object(self.helper, "validate_checkpoint"))
        checkpoint.return_value = copy.deepcopy(self.checkpoint_evidence)
        if checkpoint_error:
            checkpoint.side_effect = ValueError("synthetic checkpoint rejected")
        def git(argv, **kwargs):
            assert argv == ["git", "rev-parse", "HEAD"] and kwargs == {"cwd": self.root}
            return (head or self.helper.SOURCE).encode()
        git_mock = stack.enter_context(patch.object(self.helper.subprocess, "check_output",
                                                   side_effect=git))
        return checkpoint, git_mock


def context_tests(helper):
    cases = []
    with tempfile.TemporaryDirectory(prefix="synthetic-square-diagnostic-context-") as tmp:
        fixture = ContextFixture(Path(tmp), helper)
        mutations = [
            ("actual_context_first_module_accepted", None),
            ("actual_context_last_module_with_previous_reports_accepted", None),
            ("unapplied_source_rejected", lambda p, s: p.update(status="reviewed")),
            ("wrong_integration_source_rejected", lambda p, s: p.update(integration_commit="0" * 40)),
            ("wrong_candidate_rejected", lambda p, s: p.update(candidate="0" * 40)),
            ("wrong_control_rejected", lambda p, s: p.update(control="0" * 40)),
            ("wrong_numerical_run_rejected", lambda p, s: p.update(numerical_run=1)),
            ("changed_final_order_rejected", lambda p, s: p["final_modules"].reverse()),
            ("changed_final_hash_rejected", lambda p, s: p["reviewed_final_source_sha256"].update(
                {helper.FINAL[0]: "0" * 64})),
            ("support_not_prepared_rejected", lambda p, s: s.update(status="building")),
            ("wrong_support_source_rejected", lambda p, s: s.update(integration_commit="0" * 40)),
            ("support_leaf_hash_flag_rejected", lambda p, s: s.update(
                restored_leaf_output_hashes_unchanged=False)),
            ("missing_graph_entry_rejected", lambda p, s: p["support_preparation"]["graph"].pop(
                "Synthetic.Shared345")),
            ("missing_support_entry_rejected", lambda p, s: p["support_preparation"][
                "support_modules"].pop()),
            ("support_report_order_rejected", lambda p, s: s["modules"].reverse()),
            ("missing_protected_leaf_rejected", lambda p, s: p["protected_leaf_outputs"].pop(
                "synthetic-leaves/output-1589.bin")),
        ]
        for label, mutate in mutations:
            fixture.reset()
            plan, support = copy.deepcopy(fixture.plan), copy.deepcopy(fixture.support)
            if mutate:
                mutate(plan, support)
            fixture.write(plan, support)
            module = helper.FINAL[-1] if "last_module" in label else helper.FINAL[0]
            with ExitStack() as stack:
                checkpoint, _ = fixture.patches(stack)
                try:
                    context = helper.validate_context(fixture.report, module)
                except ValueError:
                    assert mutate is not None, label
                else:
                    assert mutate is None and context["module"] == module, label
                    assert context["completed_support_outputs"] == fixture.checkpoint_evidence[
                        "manifest"]["outputs"]
                checkpoint.assert_called_once_with(fixture.report, fixture.root)
            cases.append({"name": label, "status": "pass"})
        extra = ["unknown_module", "checkpoint_validator_rejection", "wrong_git_head",
                 "missing_checkpoint", "symlink_checkpoint", "previous_failed",
                 "previous_wrong_source", "previous_wrong_checkpoint", "previous_missing",
                 "previous_wrong_output_hash", "previous_wrong_output_size",
                 "changed_graph_source", "changed_leaf_output", "symlink_leaf_output",
                 "changed_completed_support_output"]
        for name in extra:
            fixture.reset()
            module = helper.FINAL[-1] if name.startswith("previous") else helper.FINAL[0]
            previous = fixture.previous_path(helper.FINAL[0])
            if name == "missing_checkpoint":
                fixture.checkpoint.unlink()
            elif name == "symlink_checkpoint":
                fixture.checkpoint.unlink()
                fixture.checkpoint.symlink_to(fixture.source)
            elif name.startswith("previous_"):
                if name == "previous_missing":
                    previous.unlink()
                else:
                    report = json.loads(previous.read_text())
                    if name.startswith("previous_wrong_output"):
                        output = next(iter(report["final_output_files"].values()))
                        if name.endswith("hash"):
                            output["sha256"] = "0" * 64
                        else:
                            output["bytes"] += 1
                    else:
                        key = {"previous_failed": "status", "previous_wrong_source": "source_sha256",
                               "previous_wrong_checkpoint": "support_checkpoint_sha256"}[name]
                        report[key] = "failed" if key == "status" else "0" * 64
                    json_file(previous, report)
            elif name == "changed_graph_source":
                fixture.final_path.write_bytes(b"changed synthetic final source")
            elif name == "changed_leaf_output":
                fixture.leaf.write_bytes(b"changed synthetic leaf output")
            elif name == "symlink_leaf_output":
                fixture.leaf.unlink()
                fixture.leaf.symlink_to(fixture.source)
            elif name == "changed_completed_support_output":
                fixture.output.write_bytes(b"changed synthetic support output")
            with ExitStack() as stack:
                checkpoint, git = fixture.patches(stack, head="0" * 40 if name == "wrong_git_head"
                    else None, checkpoint_error=name == "checkpoint_validator_rejection")
                try:
                    helper.validate_context(fixture.report,
                                            "Synthetic.Unknown" if name == "unknown_module" else module)
                except (ValueError, FileNotFoundError):
                    pass
                else:
                    raise AssertionError(name + " was accepted")
                if name == "unknown_module":
                    checkpoint.assert_not_called()
                if name == "checkpoint_validator_rejection":
                    git.assert_not_called()
            cases.append({"name": name + "_stops_context", "status": "pass"})
    return cases


def build_tests(helper):
    cases = []
    variants = [("actual_deps_then_build_order", None, None),
                ("deps_failure_stops_before_build", "deps", ValueError),
                ("build_failure_preserves_completed_deps", "build", ValueError),
                ("deps_interruption_persisted", "deps", helper.Terminated),
                ("build_interruption_persisted", "build", helper.Terminated),
                ("leaf_change_after_deps_stops_build", "deps", "leaf"),
                ("source_change_after_build_fails", "build", "source"),
                ("support_output_change_after_deps_stops_build", "deps", "support"),
                ("checkpoint_change_after_deps_stops_build", "deps", "checkpoint")]
    for label, stage_to_change, change in variants:
        with tempfile.TemporaryDirectory(prefix="synthetic-square-diagnostic-build-") as tmp:
            root, report_dir = Path(tmp), Path(tmp) / "reports"
            report_dir.mkdir()
            checkpoint = report_dir / "support-checkpoint/support-checkpoint.json"
            json_file(checkpoint, {"synthetic_checkpoint_only": True})
            files = {}
            for name in ["source", "leaf", "support"]:
                path = root / (name + ".fixture")
                path.write_bytes(("synthetic " + name).encode())
                files[name] = {"path": path.name, "sha256": sha(path.read_bytes())}
            module = helper.FINAL[0]
            context = {"plan": {"support_preparation": {"graph": {"synthetic": files["source"]}},
                "protected_leaf_outputs": {files["leaf"]["path"]: files["leaf"]}},
                "completed_support_outputs": {files["support"]["path"]: files["support"]},
                "module": module, "integration_commit": helper.SOURCE,
                "source_sha256": "1" * 64,
                "support_checkpoint_sha256": sha(checkpoint.read_bytes())}
            calls, events = [], []
            def stream(argv, log, timing, called_module, stage):
                assert called_module == module
                calls.append((stage, argv))
                assert json.loads((report_dir / "assembly-logs" / (module + ".json")).read_text())[
                    "status"] == "building"
                if stage == stage_to_change:
                    if change in [ValueError, helper.Terminated]:
                        raise change("synthetic " + stage + " failure")
                    if change == "checkpoint":
                        checkpoint.write_bytes(b"changed synthetic checkpoint")
                    else:
                        (root / files[change]["path"]).write_bytes(b"changed synthetic evidence")
                return {"stage": stage, "argv": argv, "returncode": 0}
            with patch.object(helper, "ROOT", root), \
                    patch.object(helper, "validate_context", return_value=context), \
                    patch.object(helper, "final_outputs", return_value={
                        "synthetic-final-output.bin": {"sha256": "2" * 64, "bytes": 10}}), \
                    patch.object(helper, "stream_command", side_effect=stream), \
                    patch.object(helper, "emit", side_effect=lambda event, **kw: events.append(
                        {"event": event, **kw})):
                try:
                    helper.build_module(report_dir, module)
                except (ValueError, helper.Terminated):
                    assert change is not None, label
                else:
                    assert change is None, label
            report = json.loads((report_dir / "assembly-logs" / (module + ".json")).read_text())
            expected = ["deps"] if stage_to_change == "deps" else ["deps", "build"]
            assert [stage for stage, _ in calls] == expected
            assert calls[0][1] == ["lake", "--no-build", "build", "+" + module + ":deps"]
            if len(calls) == 2:
                assert calls[1][1] == ["lake", "build", module]
            status = "built" if change is None else ("interrupted" if change is helper.Terminated
                                                       else "failed")
            assert report["status"] == status and report["finished_utc"]
            if change is None:
                assert report["final_output_files"] == {
                    "synthetic-final-output.bin": {"sha256": "2" * 64, "bytes": 10}}
            assert report["control_script_sha256"] == helper.digest(helper.SCRIPT)
            assert events[-1]["event"] == "module-end" and events[-1]["status"] == status
            if change:
                assert report["exception"]["type"] == ("Terminated" if change is helper.Terminated
                                                         else "ValueError")
            cases.append({"name": label, "status": "pass", "synthetic_stages": expected})
    with tempfile.TemporaryDirectory(prefix="synthetic-square-diagnostic-repeat-") as tmp:
        root = Path(tmp)
        module = helper.FINAL[0]
        path = root / "assembly-logs" / (module + ".json")
        json_file(path, {"old_attempt": "immutable synthetic evidence"})
        before = path.read_bytes()
        with patch.object(helper, "validate_context", return_value={}), \
                patch.object(helper, "stream_command") as stream:
            try:
                helper.build_module(root, module)
            except ValueError as exc:
                assert "overwrite" in str(exc)
            else:
                raise AssertionError("Repeated attempt overwritten")
            stream.assert_not_called()
        assert path.read_bytes() == before
    cases.append({"name": "repeat_attempt_rejected_without_overwrite", "status": "pass"})
    with tempfile.TemporaryDirectory(prefix="synthetic-square-diagnostic-precheck-") as tmp:
        with patch.object(helper, "validate_context", side_effect=ValueError("invalid context")), \
                patch.object(helper, "stream_command") as stream:
            try:
                helper.build_module(Path(tmp), helper.FINAL[0])
            except ValueError:
                pass
            else:
                raise AssertionError("Context rejection did not propagate")
            stream.assert_not_called()
        assert not (Path(tmp) / "assembly-logs").exists()
    cases.append({"name": "context_rejection_precedes_attempt_and_process", "status": "pass"})
    return cases


class OutputCapture(io.StringIO):
    def __init__(self):
        super().__init__()
        self.buffer = io.BytesIO()


class SyntheticProcess:
    def __init__(self, returncode, output):
        read_fd, write_fd = os.pipe()
        os.write(write_fd, output)
        os.close(write_fd)
        self.stdout = os.fdopen(read_fd, "rb", buffering=0)
        self.pid = 987654321  # Never passed to an unmocked process/signal operation.
        self.returncode = returncode
    def wait(self, timeout=None):
        return self.returncode
    def poll(self):
        return self.returncode


def streaming_tests(helper):
    cases = []
    for label, rc, time_text in [("stream_success_visible_and_durable", 0, "Exit status: 0\n"),
                                ("stream_nonzero_exit_persisted", 3, "Exit status: 3\n"),
                                ("time_disagrees_with_success_rejected", 0, "Exit status: 1\n"),
                                ("missing_time_report_rejected", 0, None)]:
        with tempfile.TemporaryDirectory(prefix="synthetic-square-diagnostic-stream-") as tmp:
            root = Path(tmp)
            log, timing = root / "command.log", root / "command.time"
            output = b"synthetic diagnostic bytes\n"
            process = SyntheticProcess(rc, output)
            events, calls = [], []
            capture = OutputCapture()
            def popen(argv, **kwargs):
                assert kwargs == {"stdout": subprocess.PIPE, "stderr": subprocess.STDOUT,
                                  "start_new_session": True}
                calls.append(argv)
                if time_text is not None:
                    timing.write_text(time_text)
                return process
            with patch.object(helper.subprocess, "Popen", side_effect=popen), \
                    patch.object(helper.os, "killpg") as kill, \
                    patch.object(helper, "emit", side_effect=lambda event, **kw: events.append(
                        {"event": event, **kw}) or events[-1]), \
                    patch.object(helper.sys, "stdout", capture):
                try:
                    result = helper.stream_command(["synthetic-command"], log, timing,
                                                   helper.FINAL[0], "build", heartbeat_seconds=0)
                except ValueError:
                    assert label != "stream_success_visible_and_durable", label
                else:
                    assert label == "stream_success_visible_and_durable" and result["returncode"] == 0
                kill.assert_not_called()
            process.stdout.close()
            assert len(calls) == 1 and calls[0] == ["/usr/bin/time", "-v", "-o", str(timing),
                                                  "synthetic-command"]
            assert log.read_bytes() == output == capture.buffer.getvalue()
            persisted = json.loads(log.with_suffix(".json").read_text())
            assert persisted["end"]["returncode"] == rc
            assert persisted["end"]["interrupted"] is False
            assert any(event["event"] == "command-heartbeat" for event in events)
            cases.append({"name": label, "status": "pass"})
    for escalate in [False, True]:
        with tempfile.TemporaryDirectory(prefix="synthetic-square-diagnostic-signal-") as tmp:
            log, timing = Path(tmp) / "command.log", Path(tmp) / "command.time"
            process = SyntheticProcess(None, b"")
            kills, events = [], []
            def wait(timeout=None):
                if escalate and timeout is not None:
                    raise subprocess.TimeoutExpired("synthetic process", timeout)
                process.returncode = -9 if escalate else -15
                return process.returncode
            process.wait = wait
            class InterruptedSelector:
                def __enter__(self): return self
                def __exit__(self, *args): return False
                def register(self, *args): pass
                def get_map(self): return {1: True}
                def select(self, *args): raise helper.Terminated("synthetic signal")
            with patch.object(helper.subprocess, "Popen", return_value=process), \
                    patch.object(helper.selectors, "DefaultSelector", InterruptedSelector), \
                    patch.object(helper.os, "killpg", side_effect=lambda pid, sig: kills.append((pid, sig))), \
                    patch.object(helper, "emit", side_effect=lambda event, **kw: events.append(
                        {"event": event, **kw}) or events[-1]):
                try:
                    helper.stream_command(["synthetic-command"], log, timing, helper.FINAL[0], "build")
                except helper.Terminated:
                    pass
                else:
                    raise AssertionError("Interruption swallowed")
            process.stdout.close()
            assert kills == [(process.pid, signal.SIGTERM)] + (
                [(process.pid, signal.SIGKILL)] if escalate else [])
            persisted = json.loads(log.with_suffix(".json").read_text())
            assert persisted["end"]["interrupted"] is True
            cases.append({"name": "interruption_kill_escalation_persisted" if escalate else
                          "interruption_term_and_status_persisted", "status": "pass"})
    return cases


def cli_tests(helper):
    cases = []
    for label, exception, expected in [("cli_success_returns0", None, 0),
                                       ("cli_interruption_returns143", helper.Terminated("synthetic"), 143),
                                       ("cli_error_returns1", ValueError("synthetic"), 1)]:
        with patch.object(sys, "argv", [str(helper.SCRIPT), "--report-dir", "/synthetic/report",
                                        "--module", helper.FINAL[0]]), \
                patch.object(helper.signal, "signal"), \
                patch.object(helper, "build_module", side_effect=exception) as build, \
                patch.object(helper, "emit"):
            assert helper.main() == expected
            build.assert_called_once_with(Path("/synthetic/report"), helper.FINAL[0])
        cases.append({"name": label, "status": "pass"})
    with patch.object(sys, "argv", [str(helper.SCRIPT), "--report-dir", "/synthetic/report",
                                    "--module", "Synthetic.Unknown"]), \
            patch.object(helper, "build_module") as build, patch.object(sys, "stderr", io.StringIO()):
        try:
            helper.main()
        except SystemExit as exc:
            assert exc.code == 2
        else:
            raise AssertionError("Unknown CLI module accepted")
        build.assert_not_called()
    cases.append({"name": "cli_unknown_module_rejected_without_build", "status": "pass"})
    return cases


def output_inventory_tests(helper):
    cases = []
    with tempfile.TemporaryDirectory(prefix="synthetic-square-final-outputs-") as tmp:
        root = Path(tmp)
        names = [f"synthetic-final-output-{i}.bin" for i in range(15)]
        for name in names:
            (root / name).write_bytes(("synthetic output " + name).encode())
        calls = []
        def module_outputs(module):
            assert module == helper.FINAL[0]
            calls.append(module)
            return names
        control = types.SimpleNamespace(module_outputs=module_outputs)
        with patch.object(helper, "ROOT", root), \
                patch.object(helper, "load_checkpoint_control", return_value=control):
            actual = helper.final_outputs(helper.FINAL[0])
            assert actual == {name: {"sha256": sha((root / name).read_bytes()),
                                     "bytes": (root / name).stat().st_size} for name in names}
            assert len(actual) == 15 and calls == [helper.FINAL[0]]
            cases.append({"name": "actual_final_output_hash_size_inventory", "status": "pass"})
            (root / names[0]).unlink()
            try:
                helper.final_outputs(helper.FINAL[0])
            except ValueError:
                pass
            else:
                raise AssertionError("Missing final output accepted")
            cases.append({"name": "missing_final_output_rejected", "status": "pass"})
            (root / names[0]).symlink_to(root / names[1])
            try:
                helper.final_outputs(helper.FINAL[0])
            except ValueError:
                pass
            else:
                raise AssertionError("Symlink final output accepted")
            cases.append({"name": "symlink_final_output_rejected", "status": "pass"})
    return cases


def test(helper_path):
    helper = load_helper(helper_path)
    # All external-process APIs not explicitly mocked in a test fail closed.
    def forbidden(*args, **kwargs):
        raise AssertionError("Synthetic test attempted an external process")
    with patch.object(subprocess, "run", forbidden), \
            patch.object(subprocess, "check_output", forbidden), \
            patch.object(subprocess, "Popen", forbidden):
        cases = (context_tests(helper) + build_tests(helper) + streaming_tests(helper)
                 + cli_tests(helper) + output_inventory_tests(helper))
    return {"status": "actual_diagnostic_helper_synthetic_tests_pass", "helper": str(helper_path),
            "helper_sha256": sha(helper_path.read_bytes()), "cases": cases,
            "external_processes_executed": 0, "proof_commands_executed": 0,
            "source_transitions_executed": 0, "restorations_executed": 0,
            "checkpoint_validator_stubbed_only_for_context_unit_tests": True,
            "resource_or_proof_acceptance_inferred": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("helper", nargs="?", type=Path,
                        default=Path(__file__).resolve().with_name("diagnose-square-assembly.py"))
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = test(args.helper.resolve())
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "tests": len(report["cases"]),
                      "helper": report["helper"], "report": str(args.report) if args.report else None}))


if __name__ == "__main__":
    main()
