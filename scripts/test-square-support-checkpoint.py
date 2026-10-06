#!/usr/bin/env python3
"""Synthetic checkpoint guard tests; no Lean, network, real outputs or restoration."""

import copy
from contextlib import contextmanager
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("square_checkpoint",
                                            HERE / "checkpoint-square-support.py")
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
FINAL = ["PartialBalayage.Maximal.Square.GeneratorLeafBlocks",
         "PartialBalayage.Maximal.Square.GeneratorInteriorPositivity",
         "PartialBalayage.Maximal.Square.SquarePositiveSource",
         "PartialBalayage.Maximal.SquareWeakBounds"]


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True) + "\n")


class CheckpointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="synthetic-square-support-")
        cls.base = Path(cls.temporary.name)
        cls.root = cls.base / "source"
        cls.report_dir = cls.base / "evidence/square-numerical"
        cls.numeric = [CHECK.PREFIX + str(n) for n in range(106)] + [
            "PartialBalayage.Fixture.Numeric" + str(n) for n in range(240)]
        cls.support = ["PartialBalayage.Fixture.Support" + str(n) for n in range(367)]
        graph = {}
        for module in cls.numeric + cls.support + FINAL:
            path = module.replace(".", "/") + ".lean"
            file = cls.root / path
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text("module\n-- synthetic fixture " + module + "\n")
            graph[module] = {"path": path, "sha256": CHECK.digest(file), "imports": [],
                             "source_commit": CHECK.CANDIDATE if module in cls.numeric
                             else CHECK.SOURCE}
        closure = {n: {k: v for k, v in graph[n].items() if k != "source_commit"}
                   for n in cls.numeric}
        cls.expected = {"closure": closure, "final_modules": FINAL,
                        "reviewed_final_source_sha256": {n: graph[n]["sha256"] for n in FINAL},
                        "support_preparation": {"graph": graph, "support_modules": cls.support,
                            "root_inclusive_project_module_count": 717, "numeric_module_count": 346,
                            "support_module_count": 367, "final_assembly_count": 4, "roots": FINAL,
                            "numeric_intersection_count": 346}}
        pins = {"lean-toolchain": CHECK.TOOLCHAIN + "\n",
                "lakefile.toml": 'rev = "' + CHECK.MATHLIB + '"\n',
                "lake-manifest.json": json.dumps({"packages": [{"name": "mathlib",
                                                               "rev": CHECK.MATHLIB}]})}
        for name, text in pins.items():
            (cls.root / name).write_text(text)
        cls.context = {"source_commit": CHECK.SOURCE, "workflow_control_commit": "a" * 40,
                       "run_id": 12345, "run_attempt": 1, "job": "integrate",
                       "repository": "CoolRmal/partial-balayage-lean",
                       "candidate": CHECK.CANDIDATE,
                       "numeric_control_commit": CHECK.CONTROL,
                       "numerical_run": CHECK.NUMERICAL_RUN,
                       "toolchain": CHECK.TOOLCHAIN, "lean_commit": CHECK.LEAN_COMMIT,
                       "mathlib": CHECK.MATHLIB,
                       "pin_file_sha256": {n: CHECK.digest(cls.root / n) for n in pins},
                       "control_script_sha256": {}}
        cls.all_outputs = {}
        for module in cls.numeric + cls.support:
            for name in CHECK.module_outputs(module):
                file = cls.root / name
                file.parent.mkdir(parents=True, exist_ok=True)
                if name.endswith(".trace"):
                    write_json(file, {"outputs": {"m": True, "o": ["a", "b", "c"],
                                                  "r": "r", "rs": "rs", "c": "c", "i": "i"},
                                      "inputs": [["Lean 4.35.0, commit " + CHECK.LEAN_COMMIT, "x"],
                                                 ["Module.name: " + module, "x"]]})
                else:
                    file.write_text("synthetic output " + name + "\n")
                cls.all_outputs[name] = {"sha256": CHECK.digest(file), "bytes": file.stat().st_size}
        numeric_outputs = {n: cls.all_outputs[n] for m in cls.numeric
                           for n in CHECK.module_outputs(m)}
        protected = {n: cls.all_outputs[n] for b in range(106)
                     for n in CHECK.module_outputs(CHECK.PREFIX + str(b))}
        cls.plan = {"status": "applied", "integration_commit": CHECK.SOURCE,
                    "candidate": CHECK.CANDIDATE, "control": CHECK.CONTROL,
                    "numerical_run": CHECK.NUMERICAL_RUN, **cls.expected,
                    "protected_leaf_outputs": protected}
        records = []
        for module in cls.support:
            stem = cls.report_dir / "support-logs" / module
            stem.parent.mkdir(parents=True, exist_ok=True)
            Path(str(stem) + "-build.log").write_text("synthetic successful build\n")
            Path(str(stem) + "-deps.log").write_text("synthetic satisfied dependencies\n")
            Path(str(stem) + ".time").write_text(
                '\tCommand being timed: "lake build ' + module + '"\n\tExit status: 0\n')
            records.append({"module": module, "source_sha256": graph[module]["sha256"],
                            "wall_seconds": 0.1, "build_log": str(stem) + "-build.log",
                            "resource_time": str(stem) + ".time"})
        cls.support_report = {"status": "prepared", "integration_commit": CHECK.SOURCE,
                              "restored_leaf_output_hashes_unchanged": True,
                              "protected_leaf_outputs": 1590, "modules": records}
        cls.aggregate = {"status": "restored", "control_commit": CHECK.CONTROL,
                         "output_count": 5190, "outputs": numeric_outputs,
                         "snapshot": {"commit": CHECK.CANDIDATE, "toolchain": CHECK.TOOLCHAIN,
                             "lean_commit": CHECK.LEAN_COMMIT, "mathlib": CHECK.MATHLIB,
                             "source_hashes": cls.context["pin_file_sha256"]}}
        cls.source_run = {"id": CHECK.NUMERICAL_RUN, "head_sha": CHECK.CONTROL,
                          "status": "completed", "conclusion": "success",
                          "path": ".github/workflows/square-numerical-checks.yml",
                          "event": "workflow_dispatch"}
        for name, value in (("integration-source-report.json", cls.plan),
                            ("support-build-report.json", cls.support_report),
                            ("aggregate-outputs-report.json", cls.aggregate)):
            write_json(cls.report_dir / name, value)
        write_json(cls.report_dir.parent / "source-run.json", cls.source_run)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def checked(self):
        return CHECK.validate_reports(self.root, self.report_dir, self.expected, self.context)

    @contextmanager
    def changed(self, path, content):
        original = path.read_bytes()
        path.write_bytes(content)
        try:
            yield
        finally:
            path.write_bytes(original)

    def reject_report(self, name, mutate):
        path = self.report_dir / name
        data = CHECK.read_json(path)
        mutate(data)
        with self.changed(path, json.dumps(data).encode()):
            with self.assertRaises(ValueError):
                self.checked()

    def test_complete_actual_shape(self):
        checked = self.checked()
        self.assertEqual(len(checked["source_graph"]), 717)
        outputs = CHECK.inventory(self.root, checked)
        self.assertEqual(outputs, self.all_outputs)
        self.assertEqual(len(outputs), 10695)
        self.assertFalse(any(n in checked["numeric_modules"] + checked["support_modules"]
                             for n in FINAL))

    def test_incomplete_support_status(self):
        self.reject_report("support-build-report.json", lambda d: d.update(status="preparing"))

    def test_missing_completed_support_record(self):
        self.reject_report("support-build-report.json", lambda d: d["modules"].pop())

    def test_duplicate_support_record(self):
        self.reject_report("support-build-report.json",
                           lambda d: d["modules"].__setitem__(1, d["modules"][0]))

    def test_changed_completed_source_hash(self):
        self.reject_report("support-build-report.json",
                           lambda d: d["modules"][0].update(source_sha256="0" * 64))

    def test_changed_support_working_source(self):
        path = self.root / self.expected["support_preparation"]["graph"][self.support[0]]["path"]
        with self.changed(path, b"changed source"):
            with self.assertRaises(ValueError):
                self.checked()

    def test_changed_reviewed_final_source(self):
        path = self.root / (FINAL[0].replace(".", "/") + ".lean")
        with self.changed(path, b"changed frozen assembly"):
            with self.assertRaises(ValueError):
                self.checked()

    def test_changed_pin(self):
        with self.changed(self.root / "lean-toolchain", b"wrong toolchain"):
            with self.assertRaises(ValueError):
                self.checked()

    def test_changed_restored_pin(self):
        self.reject_report("aggregate-outputs-report.json",
                           lambda d: d["snapshot"].update(lean_commit="0" * 40))

    def test_changed_protected_leaf_hash(self):
        self.reject_report("integration-source-report.json", lambda d:
                           next(iter(d["protected_leaf_outputs"].values())).update(sha256="0" * 64))

    def test_changed_restored_leaf_output(self):
        path = self.root / CHECK.module_outputs(CHECK.PREFIX + "0")[0]
        with self.changed(path, b"changed output"):
            with self.assertRaises(ValueError):
                self.checked()

    def test_incomplete_numeric_output_inventory(self):
        self.reject_report("aggregate-outputs-report.json",
                           lambda d: d["outputs"].pop(next(iter(d["outputs"]))))

    def test_nonzero_actual_exit(self):
        path = self.report_dir / ("support-logs/" + self.support[0] + ".time")
        timed = ('Command being timed: "lake build ' + self.support[0] + '"\n').encode()
        with self.changed(path, timed + b"Exit status: 143\n"):
            with self.assertRaisesRegex(ValueError, "actual successful exit"):
                self.checked()

    def test_missing_actual_exit(self):
        path = self.report_dir / ("support-logs/" + self.support[0] + ".time")
        timed = ('Command being timed: "lake build ' + self.support[0] + '"\n').encode()
        with self.changed(path, timed + b"Maximum resident set size: 100\n"):
            with self.assertRaisesRegex(ValueError, "actual successful exit"):
                self.checked()

    def test_missing_actual_command(self):
        path = self.report_dir / ("support-logs/" + self.support[0] + ".time")
        with self.changed(path, b"Exit status: 0\n"):
            with self.assertRaises(ValueError):
                self.checked()

    def test_wrong_actual_command(self):
        path = self.report_dir / ("support-logs/" + self.support[0] + ".time")
        with self.changed(path, b'Command being timed: "true"\nExit status: 0\n'):
            with self.assertRaises(ValueError):
                self.checked()

    def test_foreign_log_path(self):
        self.reject_report("support-build-report.json",
                           lambda d: d["modules"][0].update(build_log="/tmp/foreign.log"))

    def test_compiler_error_in_success_record(self):
        path = self.report_dir / ("support-logs/" + self.support[0] + "-build.log")
        with self.changed(path, b"error: synthetic failure\n"):
            with self.assertRaises(ValueError):
                self.checked()

    def test_failed_numerical_run(self):
        path = self.report_dir.parent / "source-run.json"
        data = copy.deepcopy(self.source_run)
        data["conclusion"] = "failure"
        with self.changed(path, json.dumps(data).encode()):
            with self.assertRaises(ValueError):
                self.checked()

    def test_missing_support_output(self):
        path = self.root / CHECK.module_outputs(self.support[0])[0]
        data = path.read_bytes()
        path.unlink()
        try:
            with self.assertRaises((ValueError, FileNotFoundError)):
                CHECK.inventory(self.root, self.checked())
        finally:
            path.write_bytes(data)

    def test_wrong_compiler_trace(self):
        path = self.root / CHECK.module_outputs(self.support[0])[4]
        data = CHECK.read_json(path)
        data["inputs"][0][0] = "Lean 4.35.0, commit " + "0" * 40
        with self.changed(path, json.dumps(data).encode()):
            with self.assertRaises(ValueError):
                CHECK.inventory(self.root, self.checked())

    def test_symlink_output(self):
        path = self.root / CHECK.module_outputs(self.support[0])[0]
        data = path.read_bytes()
        path.unlink()
        path.symlink_to(self.root / "lean-toolchain")
        try:
            with self.assertRaises(ValueError):
                CHECK.inventory(self.root, self.checked())
        finally:
            path.unlink()
            path.write_bytes(data)

    def test_unsafe_paths(self):
        for name in ("../lean-toolchain", "/tmp/file", "a/../b", "a\\b", "./lean-toolchain"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                CHECK.regular(self.root, name)

    def test_duplicate_json(self):
        path = self.report_dir / "support-build-report.json"
        with self.changed(path, b'{"status":"prepared","status":"prepared"}'):
            with self.assertRaises(ValueError):
                self.checked()

    @contextmanager
    def runtime_fixture(self):
        control = self.base / "control"
        control.mkdir(exist_ok=True)
        scripts = {"scripts/checkpoint-square-support.py": b"# committed checkpoint control\n",
                   "scripts/prepare-square-integration.py": b"# committed preparation control\n"}
        for name, data in scripts.items():
            file = control / name
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_bytes(data)
        environment = {"GITHUB_REPOSITORY": "CoolRmal/partial-balayage-lean",
                       "GITHUB_SHA": "a" * 40, "GITHUB_RUN_ID": "12345",
                       "GITHUB_RUN_ATTEMPT": "1", "GITHUB_JOB": "integrate",
                       "NUMERICAL_COMMIT": CHECK.CANDIDATE, "CONTROL_COMMIT": CHECK.CONTROL,
                       "NUMERICAL_RUN": str(CHECK.NUMERICAL_RUN)}
        state = {"source": CHECK.SOURCE, "control": "a" * 40, "mathlib": CHECK.MATHLIB}
        pins = {name: (self.root / name).read_bytes() for name in CHECK.PIN_FILES}

        def git(root, *args):
            if args == ("rev-parse", "HEAD"):
                return (state["control"] if root == control else state["source"]).encode()
            if args[0] == "show":
                commit, name = args[1].split(":", 1)
                return scripts[name] if root == control else pins[name]
            if args == ("-C", ".lake/packages/mathlib", "rev-parse", "HEAD"):
                return state["mathlib"].encode()
            if args == ("-C", ".lake/packages/mathlib", "diff", "--exit-code", "HEAD", "--"):
                if state.get("dirty"):
                    raise subprocess.CalledProcessError(1, ["git", *args])
                return b""
            raise AssertionError("Unexpected command: " + str(args))

        with patch.object(CHECK, "command", side_effect=git):
            yield control, environment, state

    def test_runtime_exact_run_source_control_pins(self):
        with self.runtime_fixture() as (control, environment, state):
            context = CHECK.runtime_context(self.root, control, environment)
            self.assertEqual(context["run_id"], 12345)
            self.assertEqual(context["source_commit"], CHECK.SOURCE)
            self.assertEqual(context["workflow_control_commit"], "a" * 40)

    def test_runtime_missing_or_wrong_identity(self):
        cases = {"GITHUB_RUN_ID": "0", "GITHUB_RUN_ATTEMPT": "",
                 "GITHUB_REPOSITORY": "other/repo", "GITHUB_SHA": "b" * 40,
                 "GITHUB_JOB": "", "NUMERICAL_RUN": "123", "NUMERICAL_COMMIT": "b" * 40}
        with self.runtime_fixture() as (control, environment, state):
            for key, value in cases.items():
                changed = dict(environment, **{key: value})
                with self.subTest(key=key), self.assertRaises(ValueError):
                    CHECK.runtime_context(self.root, control, changed)

    def test_runtime_changed_installed_mathlib(self):
        with self.runtime_fixture() as (control, environment, state):
            state["mathlib"] = "b" * 40
            with self.assertRaises(ValueError):
                CHECK.runtime_context(self.root, control, environment)

    def test_runtime_dirty_installed_mathlib(self):
        with self.runtime_fixture() as (control, environment, state):
            state["dirty"] = True
            with self.assertRaises(subprocess.CalledProcessError):
                CHECK.runtime_context(self.root, control, environment)

    def test_runtime_uncommitted_control_script(self):
        with self.runtime_fixture() as (control, environment, state):
            path = control / "scripts/checkpoint-square-support.py"
            with self.changed(path, b"changed control"):
                with self.assertRaises(ValueError):
                    CHECK.runtime_context(self.root, control, environment)

    def test_runtime_wrong_source_commit(self):
        with self.runtime_fixture() as (control, environment, state):
            state["source"] = "b" * 40
            with self.assertRaises(ValueError):
                CHECK.runtime_context(self.root, control, environment)

    def tar_stream(self, entries):
        stream = io.BytesIO()
        with tarfile.open(fileobj=stream, mode="w", format=tarfile.USTAR_FORMAT) as tar:
            for name, data, kind in entries:
                info = tarfile.TarInfo(name)
                info.type = kind
                info.size = len(data) if kind == tarfile.REGTYPE else 0
                info.linkname = "elsewhere" if kind != tarfile.REGTYPE else ""
                tar.addfile(info, io.BytesIO(data) if kind == tarfile.REGTYPE else None)
        stream.seek(0)
        return stream

    def test_archive_exact_regular_members(self):
        name, data = ".lake/build/lib/lean/Test.olean", b"fixture"
        expected = {name: {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}}
        CHECK.inspect_tar(self.tar_stream([(name, data, tarfile.REGTYPE)]), expected)

    def test_archive_missing_extra_unsafe_duplicate_changed_and_links(self):
        name, data = ".lake/build/lib/lean/Test.olean", b"fixture"
        expected = {name: {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}}
        good = (name, data, tarfile.REGTYPE)
        cases = [[], [good, ("extra", data, tarfile.REGTYPE)],
                 [good, ("../unsafe", data, tarfile.REGTYPE)], [good, good],
                 [(name, b"changed", tarfile.REGTYPE)],
                 [(name, b"", tarfile.SYMTYPE)], [(name, b"", tarfile.LNKTYPE)]]
        for entries in cases:
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                CHECK.inspect_tar(self.tar_stream(entries), expected)

    def test_hidden_concatenated_tar_member(self):
        name, data = ".lake/build/lib/lean/Test.olean", b"fixture"
        expected = {name: {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}}
        one = self.tar_stream([(name, data, tarfile.REGTYPE)]).getvalue()
        two = self.tar_stream([("extra", data, tarfile.REGTYPE)]).getvalue()
        with self.assertRaises(ValueError):
            CHECK.inspect_tar(io.BytesIO(one + two), expected)

    @unittest.skipUnless(shutil.which("zstd"), "zstd unavailable; pure archive guards still tested")
    def test_synthetic_full_pack_and_existing_checkpoint(self):
        destination = self.report_dir / "support-checkpoint"
        with patch.object(CHECK, "runtime_context", return_value=self.context), \
                patch.object(CHECK, "expected_plan", return_value=self.expected):
            try:
                manifest = CHECK.pack(self.root, self.base, self.report_dir, {})
                self.assertEqual(manifest["output_count"], 10695)
                result = CHECK.validate_existing_checkpoint(self.report_dir, self.root)
                self.assertEqual(result["manifest"], manifest)
                target = self.root / CHECK.module_outputs(self.support[0])[0]
                with self.changed(target, b"changed since checkpoint"):
                    with self.assertRaises(ValueError):
                        CHECK.validate_existing_checkpoint(self.report_dir, self.root)
                checkpoint = destination / "support-checkpoint.json"
                bad = copy.deepcopy(manifest)
                bad["context"]["run_id"] += 1
                with self.changed(checkpoint, json.dumps(bad).encode()):
                    with self.assertRaises(ValueError):
                        CHECK.validate_existing_checkpoint(self.report_dir, self.root)
            finally:
                if destination.exists():
                    shutil.rmtree(destination)


if __name__ == "__main__":
    unittest.main(verbosity=2)
