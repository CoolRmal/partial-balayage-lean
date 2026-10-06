#!/usr/bin/env python3
"""Exercise the real guard main/execute flow with explicitly synthetic evidence.

No Lean commands, Git switches, or project source writes occur. Only subprocess
and checkout/archive boundaries are mocked. The real snapshot/report validators,
main dispatch, compatibility recheck, cache hashing, and final report emission
run against temporary fixture files. Fixture reports are not proof evidence.

Usage: python3 scripts/test-rewarm-compatible-generator-cache.py --guard PATH
"""

import argparse
import contextlib
import copy
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock

NEW_COMMIT = "dde634e918bcbba00881018b205dea4172d2ee5f"
CONTROL_COMMIT = "c" * 40


def load_guard(path, previous_bug=False):
    source = path.read_text()
    if previous_bug:
        fixed = """        if args.execute_isolated_switch:
            execute(args.root, old, new, args, compatibility)
        else:
            compatibility["status"] = "compatible-sources-only"
"""
        broken = """        compatibility["status"] = "compatible-sources-only"
        if args.execute_isolated_switch:
            execute(args.root, old, new, args, compatibility)
"""
        if source.count(fixed) != 1:
            raise ValueError("The reviewed fixed dispatch has changed; inspect regression mutation")
        source = source.replace(fixed, broken)
    module = types.ModuleType("warm_guard_execution_fixture")
    module.__file__ = str(path)
    exec(compile(source, str(path), "exec"), module.__dict__)
    return module


class Flow:
    def __init__(self, guard, temporary, failure=None):
        self.g = guard
        self.base = Path(temporary).resolve()
        self.root = self.base / "isolated-fixture-checkout"
        self.runner = self.base / "runner-temp"
        self.root.mkdir()
        self.runner.mkdir()
        self.report_path = self.base / "compatibility-result.json"
        self.head = guard.OLD_COMMIT
        self.commands, self.closes, self.archives = [], [], []
        self.failure = failure
        self.comparisons = 0
        coordinates = list(range(32)) + list(range(32, 88, 2)) + [88]
        self.roots = [guard.NAMESPACE + "." + n for n in (
            "GeneratorLeafFastCheck", "GeneratorRadialRoots",
            "GeneratorPartitionRectangles", "GeneratorLeafSparseCheck")]
        self.roots += [guard.NAMESPACE + f".Data.GeneratorCoordinates{n}" for n in coordinates]
        self.facts = {
            "old_commit": guard.OLD_COMMIT, "new_commit": NEW_COMMIT,
            "shared_roots": self.roots, "shared_source_count": 240,
            "shared_source_hashes": {f"Fixture/Shared{n}.lean": "a" * 64 for n in range(240)},
            "external_imports": ["Mathlib.SyntheticFixture"],
            "pin_hashes": {p: "b" * 64 for p in guard.PINS},
        }
        self.download = self.runner / "square-numerical-download"
        self.download.mkdir()
        self.seed_manifest_path = self.download / "warm-manifest.json"
        self.seed_archive = self.download / "warm-outputs.tar.zst"
        self.seed_archive.write_bytes(b"SYNTHETIC FIXTURE; NOT A LEAN BUILD ARTIFACT")
        old = self.revision(self.root, guard.OLD_COMMIT)
        self.seed_manifest = {**guard.expected_snapshot(old),
                              "archive_sha256": guard.file_digest(self.seed_archive)}
        self.seed_bytes = json.dumps(self.seed_manifest, sort_keys=True).encode()
        self.seed_manifest_path.write_bytes(self.seed_bytes)
        self.cache = self.root / ".lake/build/lib/lean/Fixture.olean"

    def revision(self, root, commit):
        flow = self

        class FixtureRevision:
            def __init__(self):
                self.root, self.commit = root, commit

            def source_hashes(self):
                # Synthetic snapshots distinguish old/new numerical sources.
                return {"Fixture/Shared.lean": "a" * 64,
                        "Fixture/Numerical.lean": "1" * 64 if commit == flow.g.OLD_COMMIT
                        else "2" * 64}

            def text(self, name):
                match = re.search(r"/GeneratorCoordinates(\d+)\.lean$", name)
                if match:
                    n = int(match.group(1))
                    labels = [n, n + 1] if 32 <= n < 88 else [n]
                    # Strings are metadata fixtures, never saved/compiled Lean sources.
                    return "\n".join(f"theorem generatorCoordinates{k}_valid" for k in labels)
                return ""

            def close(self):
                flow.closes.append(self.commit)

        return FixtureRevision()

    def compare(self, old, new, expected=240):
        self.comparisons += 1
        self.g.require((old.commit, new.commit, expected) ==
                       (self.g.OLD_COMMIT, NEW_COMMIT, 240), "Unexpected fixture comparison")
        facts = copy.deepcopy(self.facts)
        if self.failure == "changed-shared-facts" and self.comparisons == 2:
            facts["shared_source_hashes"]["Fixture/Shared0.lean"] = "f" * 64
        return facts

    def clean(self, root, commit, revision):
        self.g.require(root == self.root and self.head == commit and revision.commit == commit,
                       "Fixture checkout is at unexpected HEAD")

    def seed_identity(self, data, manifest):
        # Seed archive byte provenance is covered by the separate actual-seed tests.
        self.g.require(data == self.seed_bytes and manifest == self.seed_manifest,
                       "Synthetic seed fixture was unexpectedly relabelled")

    def archive(self, path, manifest):
        self.archives.append(path)
        self.g.require(self.g.file_digest(path) == manifest["archive_sha256"],
                       "Synthetic archive bytes differ from fixture manifest")

    def run(self, args, **kwargs):
        self.commands.append(list(args))
        if args == [sys.executable, self.g.DRIVER, "restore"]:
            self.g.require(kwargs["env"]["NUMERICAL_COMMIT"] == self.g.OLD_COMMIT,
                           "Old restore was called with the new SHA")
            if self.failure == "restore-command":
                raise subprocess.CalledProcessError(1, args)
            self.cache.parent.mkdir(parents=True)
            self.cache.write_bytes(b"SYNTHETIC CHECKED-CACHE FIXTURE")
        elif args == ["git", "switch", "--detach", NEW_COMMIT]:
            self.g.require(self.head == self.g.OLD_COMMIT, "Unexpected fixture switch ordering")
            self.head = NEW_COMMIT
            if self.failure == "changed-cache":
                self.cache.write_bytes(b"ALTERED SYNTHETIC CACHE")
        elif args == [sys.executable, self.g.DRIVER, "warm"]:
            self.g.require(self.head == NEW_COMMIT, "Fresh warm ran before the switch")
            self.g.require(kwargs["env"]["NUMERICAL_COMMIT"] == NEW_COMMIT,
                           "Fresh warm was called with the old SHA")
            self.emit_synthetic_fresh_evidence()
        else:
            raise AssertionError(f"Unexpected subprocess blocked by test: {args!r}")
        return subprocess.CompletedProcess(args, 0)

    def emit_synthetic_fresh_evidence(self):
        out = self.runner / "square-numerical"
        out.mkdir()
        new = self.revision(self.root, NEW_COMMIT)
        snapshot = self.g.expected_snapshot(new)
        archive = out / "warm-outputs.tar.zst"
        archive.write_bytes(b"SYNTHETIC FRESH FIXTURE; NOT PROOF EVIDENCE")
        manifest = {**snapshot, "archive_sha256": self.g.file_digest(archive)}
        if self.failure == "stale-fresh-manifest":
            manifest["commit"] = self.g.OLD_COMMIT
        (out / "warm-manifest.json").write_text(json.dumps(manifest))
        endpoints = self.g.expected_audits(new, self.roots)
        axioms = {name: sorted(self.g.PERMITTED) for name in endpoints}
        if self.failure == "missing-fresh-audit":
            axioms.pop(next(iter(axioms)))
        if self.failure == "unpermitted-fresh-axiom":
            axioms[next(iter(axioms))].append("sorryAx")
        report = {"status": "pass", "snapshot": snapshot,
                  "modules": [{"module": m, "seconds": 0} for m in self.roots],
                  "audit": {"seconds": 0, "axioms": axioms}}
        if self.failure == "nonpassing-fresh-report":
            report["status"] = "building"
        (out / "warm-report.json").write_text(json.dumps(report))
        if self.failure == "relabelled-old-manifest":
            self.seed_manifest_path.write_bytes(b"RELABELLED OLD FIXTURE")

    def invoke_main(self):
        args = ["guard-fixture", "--new-commit", NEW_COMMIT, "--root", str(self.root),
                "--runner-temp", str(self.runner), "--report", str(self.report_path),
                "--execute-isolated-switch"]
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.object(self.g, "Revision", side_effect=self.revision))
            stack.enter_context(mock.patch.object(self.g, "compare_shared",
                                                  side_effect=self.compare))
            stack.enter_context(mock.patch.object(self.g, "check_repository"))
            stack.enter_context(mock.patch.object(self.g, "check_control_checkout",
                                                  return_value=CONTROL_COMMIT))
            stack.enter_context(mock.patch.object(self.g, "clean_checkout_at",
                                                  side_effect=self.clean))
            stack.enter_context(mock.patch.object(self.g, "check_seed_identity",
                                                  side_effect=self.seed_identity))
            stack.enter_context(mock.patch.object(self.g, "check_archive",
                                                  side_effect=self.archive))
            stack.enter_context(mock.patch.object(self.g.subprocess, "run",
                                                  side_effect=self.run))
            repository_env = {"GITHUB_REPOSITORY": self.g.PUBLIC_REPOSITORY}
            stack.enter_context(mock.patch.dict(self.g.os.environ, repository_env))
            stack.enter_context(mock.patch.object(sys, "argv", args))
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            # The real main, execute, snapshot/report validators and cache hash routines run.
            self.g.main()

    def warm_was_invoked(self):
        return [sys.executable, self.g.DRIVER, "warm"] in self.commands


class ExecutionTests(unittest.TestCase):
    def flow(self, failure=None, previous_bug=False):
        temporary = tempfile.TemporaryDirectory(prefix="pb-rewarm-execution-", dir="/tmp")
        self.addCleanup(temporary.cleanup)
        return Flow(load_guard(GUARD_PATH, previous_bug), temporary.name, failure)

    def test_main_reaches_fresh_warm_and_emits_successful_report(self):
        flow = self.flow()
        flow.invoke_main()
        self.assertEqual(flow.commands, [
            [sys.executable, flow.g.DRIVER, "restore"],
            ["git", "switch", "--detach", NEW_COMMIT],
            [sys.executable, flow.g.DRIVER, "warm"]])
        facts = json.loads(flow.report_path.read_text())
        self.assertEqual(facts["status"], "fresh-warm-pass")
        self.assertEqual(facts["imported_audit_count"], 99)
        self.assertEqual(facts["new_commit"], NEW_COMMIT)
        self.assertEqual(facts["control_commit"], CONTROL_COMMIT)
        self.assertEqual(flow.seed_manifest_path.read_bytes(), flow.seed_bytes)
        self.assertEqual(flow.comparisons, 2)
        self.assertEqual(flow.closes, [flow.g.OLD_COMMIT, NEW_COMMIT])

    def test_previous_status_decoration_bug_is_detected(self):
        # Reinstate the exact old bug in memory; no script/source file is rewritten.
        flow = self.flow(previous_bug=True)
        with self.assertRaisesRegex(ValueError, "Compatibility facts changed"):
            flow.invoke_main()
        self.assertFalse(flow.warm_was_invoked())
        self.assertFalse(flow.report_path.exists())

    def test_changed_shared_facts_stop_before_fresh_warm(self):
        flow = self.flow("changed-shared-facts")
        with self.assertRaisesRegex(ValueError, "Compatibility facts changed"):
            flow.invoke_main()
        self.assertEqual(flow.head, NEW_COMMIT)
        self.assertFalse(flow.warm_was_invoked())
        self.assertFalse(flow.report_path.exists())

    def test_changed_cache_stops_before_fresh_warm(self):
        flow = self.flow("changed-cache")
        with self.assertRaisesRegex(ValueError, "outputs changed"):
            flow.invoke_main()
        self.assertFalse(flow.warm_was_invoked())

    def test_missing_fresh_audit_rejected_after_actual_warm_boundary(self):
        flow = self.flow("missing-fresh-audit")
        with self.assertRaisesRegex(ValueError, "all 99"):
            flow.invoke_main()
        self.assertTrue(flow.warm_was_invoked())
        self.assertFalse(flow.report_path.exists())

    def test_fresh_audit_with_unpermitted_axiom_rejected(self):
        flow = self.flow("unpermitted-fresh-axiom")
        with self.assertRaisesRegex(ValueError, "axiom basis"):
            flow.invoke_main()
        self.assertTrue(flow.warm_was_invoked())
        self.assertFalse(flow.report_path.exists())

    def test_nonpassing_fresh_report_rejected(self):
        flow = self.flow("nonpassing-fresh-report")
        with self.assertRaisesRegex(ValueError, "not a pass"):
            flow.invoke_main()
        self.assertTrue(flow.warm_was_invoked())

    def test_stale_fresh_manifest_rejected(self):
        flow = self.flow("stale-fresh-manifest")
        with self.assertRaisesRegex(ValueError, "differs in commit"):
            flow.invoke_main()
        self.assertTrue(flow.warm_was_invoked())

    def test_relabelled_old_manifest_rejected(self):
        flow = self.flow("relabelled-old-manifest")
        with self.assertRaisesRegex(ValueError, "relabelled"):
            flow.invoke_main()
        self.assertFalse(flow.report_path.exists())

    def test_failed_restore_stops_before_checkout_switch(self):
        flow = self.flow("restore-command")
        with self.assertRaises(subprocess.CalledProcessError):
            flow.invoke_main()
        self.assertEqual(flow.head, flow.g.OLD_COMMIT)
        self.assertFalse(flow.warm_was_invoked())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--guard", type=Path,
                        default=Path.cwd() / "scripts/rewarm-compatible-generator-cache.py")
    options, remaining = parser.parse_known_args()
    GUARD_PATH = options.guard.resolve()
    unittest.main(argv=[sys.argv[0], *remaining], verbosity=2)
