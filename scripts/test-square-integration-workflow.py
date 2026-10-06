#!/usr/bin/env python3
"""Test the workflow's actual inline gates using synthetic responses, without Lean."""
import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import types
from unittest.mock import patch

CANDIDATE = "dde634e918bcbba00881018b205dea4172d2ee5f"
CONTROL = "243a5bd4f80c9517e7c9f834e85c5154eeb8e9a9"
RUN = 37409981058


def inline(text, name, workflow):
    start = text.index("      - name: " + name + "\n")
    tail = text[start:].split("python3 - <<'PY'\n", 1)[1]
    body = tail.split("\n          PY", 1)[0]
    result = textwrap.dedent(body)
    compile(result, str(workflow) + ":" + name, "exec")
    return result


def test(workflow):
    text = workflow.read_text()
    assert "LEAN_NUM_THREADS" not in text
    assert f"NUMERICAL_COMMIT: {CANDIDATE}" in text
    assert f"CONTROL_COMMIT: {CONTROL}" in text
    assert f'NUMERICAL_RUN: "{RUN}"' in text
    gate = inline(text, "Require the actual complete numerical run to pass", workflow)
    names = ["Build and audit shared square dependencies",
             "Restore and audit all 106 checked numerical modules"]
    names += [f"Ordinary kernel checks, blocks {n}–{min(n+5,105)}"
              for n in range(0, 106, 6)]
    jobs = [{"name": n, "status": "completed", "conclusion": "success"} for n in names]
    run = {"id": RUN, "head_sha": CONTROL, "status": "completed", "conclusion": "success",
           "event": "workflow_dispatch", "path": ".github/workflows/square-numerical-checks.yml"}
    results = []
    with tempfile.TemporaryDirectory(prefix="synthetic-square-workflow-") as tmp:
        env = {"REPOSITORY": "CoolRmal/partial-balayage-lean", "NUMERICAL_RUN": str(RUN),
               "CONTROL_COMMIT": CONTROL, "RUNNER_TEMP": tmp}
        cases = [("exact_20_successful_jobs_accepted", run, jobs, True),
                 ("duplicate_21st_job_rejected", run, jobs + [jobs[0]], False),
                 ("missing_job_rejected", run, jobs[:-1], False),
                 ("previous_run_rejected", dict(run, id=37408678726), jobs, False),
                 ("active_run_rejected", dict(run, status="in_progress", conclusion=None), jobs, False),
                 ("wrong_control_rejected", dict(run, head_sha="0" * 40), jobs, False)]
        failed = copy.deepcopy(jobs)
        failed[4]["conclusion"] = "failure"
        cases.append(("unsuccessful_job_rejected", run, failed, False))
        for label, fake_run, fake_jobs, accept in cases:
            calls = []

            def response(argv):
                calls.append(argv)
                if argv[:2] != ["gh", "api"]:
                    raise RuntimeError("Unexpected synthetic API command")
                if argv[-1].endswith("/jobs?per_page=100"):
                    return json.dumps({"jobs": fake_jobs}).encode()
                return json.dumps(fake_run).encode()

            mock = types.ModuleType("subprocess")
            mock.check_output = response
            with patch.dict(sys.modules, {"subprocess": mock}), patch.dict(os.environ, env):
                try:
                    exec(gate, {})
                except AssertionError:
                    assert not accept, label
                else:
                    assert accept, label
            results.append({"name": label, "status": "pass", "synthetic_api_calls": len(calls)})
    modules = ["PartialBalayage.Maximal.Square.GeneratorLeafBlocks",
               "PartialBalayage.Maximal.Square.GeneratorInteriorPositivity",
               "PartialBalayage.Maximal.Square.SquarePositiveSource",
               "PartialBalayage.Maximal.SquareWeakBounds"]
    positions = []
    for module in modules:
        name = "Build assembly: " + module.rsplit(".", 1)[1]
        marker = "      - name: '" + name + "'\n"
        assert text.count(marker) == 1
        positions.append(text.index(marker))
        step = text.split(marker, 1)[1].split("\n      - ", 1)[0]
        command = step.split("        run: >-\n", 1)[1]
        assert all(line.startswith("          ") for line in command.splitlines())
        command = " ".join(line.strip() for line in command.splitlines())
        assert command == ("python3 -u .integration-control/scripts/diagnose-square-assembly.py "
                           '--report-dir "$RUNNER_TEMP/square-numerical" --module ' + module)
        results.append({"name": "actual_diagnostic_helper_invocation_" + module,
                        "status": "pass", "synthetic_process_calls": 0})
    assert positions == sorted(positions)
    assert text.index("      - name: Save the complete support checkpoint before assembly\n") < positions[0]
    assert text.index("      - name: Upload the complete support checkpoint before assembly\n") < positions[0]
    assert "Build the four actual integration modules serially" not in text
    results.append({"name": "mandatory_checkpoint_precedes_ordered_helper_invocations",
                    "status": "pass", "synthetic_process_calls": 0})
    return {"status": "actual_inline_synthetic_gates_pass", "candidate": CANDIDATE,
            "control_commit": CONTROL, "run": RUN, "proof_commands_executed": 0,
            "source_transitions_executed": 0, "restorations_executed": 0,
            "workflow_sha256": hashlib.sha256(workflow.read_bytes()).hexdigest(),
            "cases": results, "scheduling_cap_claimed": False}


def preparation_tests(workflow):
    script = Path(__file__).resolve().with_name("prepare-square-integration.py")
    spec = importlib.util.spec_from_file_location("tested_square_prepare", script)
    prepare = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(prepare)
    assert (prepare.CANDIDATE, prepare.CONTROL, prepare.RUN) == (CANDIDATE, CONTROL, RUN)
    assert list(prepare.FINAL_SHA256) == prepare.FINAL
    results = []
    fixtures = {m.replace(".", "/") + ".lean": ("synthetic source " + m).encode()
                for m in prepare.FINAL}
    hashes = {m: prepare.sha(fixtures[m.replace(".", "/") + ".lean"])
              for m in prepare.FINAL}
    for changed in [None, *prepare.FINAL]:
        data = dict(fixtures)
        if changed:
            data[changed.replace(".", "/") + ".lean"] += b" changed"
        with patch.object(prepare, "source", lambda commit, path: data[path]), \
                patch.object(prepare, "FINAL_SHA256", hashes):
            try:
                found = prepare.reviewed_final_sources("1" * 40, set(data))
            except ValueError as exc:
                assert changed is not None and "Unreviewed final draft" in str(exc)
            else:
                assert changed is None and found == hashes
        results.append({"name": "reviewed_source_hashes_accepted" if changed is None else
                        "changed_final_source_rejected_" + changed, "status": "pass"})

    # Exercise actual main: a changed reviewed draft must stop before checkout or any build.
    for changed in prepare.FINAL:
        with tempfile.TemporaryDirectory(prefix="synthetic-square-source-gate-") as tmp:
            root = Path(tmp)
            out = root / "square-numerical"
            out.mkdir()
            (root / "run.json").write_text(json.dumps({"id": RUN, "head_sha": CONTROL,
                "status": "completed", "conclusion": "success"}))
            (out / "aggregate-outputs-report.json").write_text(json.dumps({
                "status": "restored", "snapshot": {"commit": CANDIDATE, "source_hashes": {}},
                "control_commit": CONTROL, "outputs": {}}))
            def fake_git(*args):
                if args == ("rev-parse", "HEAD"):
                    return CANDIDATE.encode()
                if args[:3] == ("ls-tree", "-r", "--name-only"):
                    return "\n".join(fixtures).encode()
                raise RuntimeError("Unexpected synthetic Git command")
            def fake_source(commit, path):
                if path in fixtures:
                    return fixtures[path] + (b" changed" if path == changed.replace(".", "/") + ".lean"
                                            else b"")
                if path in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
                    return b"synthetic fixed pin"
                block = path.removesuffix(".lean").rsplit("GeneratorLeafBlocks", 1)[1]
                return ("def generatorLeafBlocks" + block + " := [\n]\n").encode()
            def forbidden(*args, **kwargs):
                raise RuntimeError("Source guard failed to reject before checkout/build")
            argv = [str(script), "--integration-commit", "1" * 40,
                    "--run-metadata", str(root / "run.json"), "--apply-after-full-pass"]
            with patch.object(prepare, "ROOT", root), patch.object(prepare, "git", fake_git), \
                    patch.object(prepare, "source", fake_source), \
                    patch.object(prepare, "closure", lambda: {}), \
                    patch.object(prepare, "FINAL_SHA256", hashes), \
                    patch.object(prepare.subprocess, "run", forbidden), \
                    patch.object(sys, "argv", argv), patch.dict(os.environ, {"RUNNER_TEMP": tmp}):
                try:
                    prepare.main()
                except ValueError as exc:
                    assert "Unreviewed final draft" in str(exc)
                else:
                    raise AssertionError("Changed final draft reached transition")
            assert not (out / "integration-source-report.json").exists()
        results.append({"name": "actual_main_rejects_before_transition_" + changed, "status": "pass"})

    shared = "PartialBalayage.SyntheticShared"
    a, b = "PartialBalayage.SyntheticA", "PartialBalayage.SyntheticB"
    leaf = prepare.PREFIX + "0"
    numeric = {m: {"path": m.replace(".", "/") + ".lean"} for m in [shared, leaf]}
    base = {shared: "", leaf: "import " + shared,
            a: "import " + b, b: "import " + shared,
            prepare.FINAL[0]: "import " + a,
            prepare.FINAL[1]: "import " + prepare.FINAL[0],
            prepare.FINAL[2]: "import " + prepare.FINAL[1],
            prepare.FINAL[3]: "import " + prepare.FINAL[2]}
    variants = [("acyclic_support_order_accepted", base, True),
                ("support_cycle_rejected", dict(base, **{b: "import " + a}), False),
                ("missing_support_import_rejected", dict(base, **{b: "import PartialBalayage.Missing"}), False),
                ("support_leaf_dependency_rejected", dict(base, **{b: "import " + leaf}), False),
                ("support_assembly_dependency_rejected", dict(base, **{b: "import " + prepare.FINAL[1]}), False),
                ("wrong_final_assembly_order_rejected", dict(base, **{
                    prepare.FINAL[2]: "import " + prepare.FINAL[3], prepare.FINAL[3]: ""}), False)]
    for label, modules, accept in variants:
        data = {m.replace(".", "/") + ".lean": s.encode() for m, s in modules.items()}
        with patch.object(prepare, "source", lambda commit, path: data[path]):
            try:
                plan = prepare.support_plan("1" * 40, set(data), numeric)
            except ValueError:
                assert not accept, label
            else:
                assert accept and plan["support_modules"] == [b, a]
        results.append({"name": label, "status": "pass"})

    support = inline(workflow.read_text(), "Prepare only the explicitly ordered support modules", workflow)
    leaf_guard = inline(workflow.read_text(), "Require every restored leaf output to remain unchanged", workflow)
    with tempfile.TemporaryDirectory(prefix="synthetic-square-support-stage-") as tmp:
        root = Path(tmp)
        out = root / "square-numerical"
        out.mkdir()
        paths = {m: root / (m + ".source") for m in [b, a]}
        for m, path in paths.items():
            path.write_text("synthetic support " + m)
        leaf_path = root / "synthetic-leaf-output"
        leaf_path.write_bytes(b"synthetic immutable output")
        plan = {"status": "applied", "candidate": CANDIDATE, "control": CONTROL,
                "numerical_run": RUN, "integration_commit": "1" * 40,
                "protected_leaf_outputs": {str(leaf_path): {"sha256": prepare.sha(leaf_path.read_bytes())}},
                "support_preparation": {"support_modules": [b, a], "graph": {
                    m: {"path": str(p), "sha256": prepare.sha(p.read_bytes())} for m, p in paths.items()}}}
        (out / "integration-source-report.json").write_text(json.dumps(plan))
        env = {"RUNNER_TEMP": tmp, "NUMERICAL_COMMIT": CANDIDATE,
               "CONTROL_COMMIT": CONTROL, "NUMERICAL_RUN": str(RUN)}
        for label, fail, mutate in [("support_stage_exact_order_accepted", False, False),
                                    ("support_deps_exit3_stops_before_build", True, False),
                                    ("support_stage_detects_changed_leaf_output", False, True)]:
            calls = []
            def fake_run(argv, **kwargs):
                calls.append(argv)
                if fail and argv[:3] == ["lake", "--no-build", "build"]:
                    raise subprocess.CalledProcessError(3, argv)
                if mutate and argv[0] == "/usr/bin/time":
                    leaf_path.write_bytes(b"changed synthetic output")
                return subprocess.CompletedProcess(argv, 0)
            mock = types.ModuleType("subprocess")
            mock.STDOUT = subprocess.STDOUT
            mock.run = fake_run
            mock.check_output = lambda argv: ("1" * 40).encode()
            leaf_path.write_bytes(b"synthetic immutable output")
            with patch.dict(sys.modules, {"subprocess": mock}), patch.dict(os.environ, env):
                try:
                    exec(support, {})
                except subprocess.CalledProcessError:
                    assert fail and len(calls) == 1
                except AssertionError:
                    assert mutate
                else:
                    assert not fail and not mutate
                    assert [x[-1] for x in calls] == ["+" + b + ":deps", b, "+" + a + ":deps", a]
            import shutil
            shutil.rmtree(out / "support-logs")
            results.append({"name": label, "status": "pass"})
        for mutate in [False, True]:
            leaf_path.write_bytes(b"changed synthetic output" if mutate else b"synthetic immutable output")
            with patch.dict(os.environ, env):
                try:
                    exec(leaf_guard, {})
                except AssertionError:
                    assert mutate
                else:
                    assert not mutate
            results.append({"name": "final_leaf_output_change_rejected" if mutate else
                            "final_leaf_output_hash_accepted", "status": "pass"})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workflow", nargs="?", type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        ".github/workflows/square-integration.yml")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = test(args.workflow)
    assert len(report["cases"]) == 12
    report["preparation_control_cases"] = preparation_tests(args.workflow)
    diagnostics_script = Path(__file__).resolve().with_name("test-square-assembly-diagnostics.py")
    spec = importlib.util.spec_from_file_location("tested_square_diagnostic_cases", diagnostics_script)
    diagnostics = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(diagnostics)
    report["diagnostic_helper"] = diagnostics.test(
        Path(__file__).resolve().with_name("diagnose-square-assembly.py"))
    encoded = json.dumps(report, indent=2) + "\n"
    if args.report:
        args.report.write_text(encoded)
    print(json.dumps({"status": report["status"], "tests": len(report["cases"]),
                      "preparation_control_tests": len(report["preparation_control_cases"]),
                      "diagnostic_helper_tests": len(report["diagnostic_helper"]["cases"]),
                      "workflow": str(args.workflow), "report": str(args.report) if args.report else None}))


if __name__ == "__main__":
    main()
