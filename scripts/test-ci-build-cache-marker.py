#!/usr/bin/env python3
"""Actual Git/cache-marker fixtures only; never invoke Lean or Lake."""
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().with_name("ci-build-cache-marker.py")
spec = importlib.util.spec_from_file_location("ci_build_cache_marker", SCRIPT)
marker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(marker)


def git(root, *args):
    return subprocess.check_output(["git", "-c", "core.hooksPath=/dev/null", "-C", str(root), *args],
                                   stderr=subprocess.PIPE).decode().strip()


class MarkerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="ordinary-ci-cache-marker-fixture-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        git(self.root, "init", "-q", "-b", "main")
        git(self.root, "config", "user.name", "Cache guard fixture")
        git(self.root, "config", "user.email", "fixture@example.invalid")
        git(self.root, "config", "commit.gpgsign", "false")
        for path in marker.PINS:
            p = self.root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("fixture input: " + path + "\n")
        for path, value in {"Main.lean": "def fixture := 0\n", ".gitignore": ".lake/\n",
                            "scripts/verify-comparator.sh": "fixture command\n",
                            ".github/workflows/ci.yml": "fixture workflow\n"}.items():
            p = self.root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(value)
        self.commit()
        self.env = {"GITHUB_SHA": self.head, "GITHUB_REPOSITORY": "fixture/repo",
                    "RUNNER_OS": "Linux", "RUNNER_ARCH": "X64", "GITHUB_RUN_ID": "1"}
        marker.operate("write", self.root, self.env)
        self.path = marker.marker_path(self.root, self.head)

    def commit(self):
        git(self.root, "add", "--all")
        git(self.root, "commit", "-q", "--no-gpg-sign", "-m", "actual fixture commit")
        self.head = git(self.root, "rev-parse", "HEAD")

    def test_exact_current_marker_accepts(self):
        self.assertEqual(marker.operate("verify", self.root, self.env)["status"], "exact-inputs-match")

    def test_same_commit_rerun_different_run_identity_accepts(self):
        self.env.update(GITHUB_RUN_ID="99", GITHUB_RUN_ATTEMPT="7")
        self.assertEqual(marker.operate("verify", self.root, self.env)["status"], "exact-inputs-match")

    def test_source_change_new_commit_rejects_old_marker(self):
        (self.root / "Main.lean").write_text("def fixture := 1\n")
        self.commit()
        self.env["GITHUB_SHA"] = self.head
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_dirty_source_rejects(self):
        (self.root / "Main.lean").write_text("changed tracked source\n")
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_dirty_dependency_pin_rejects(self):
        (self.root / "lean-toolchain").write_text("other toolchain\n")
        with self.assertRaises(ValueError):
            marker.operate("write", self.root, self.env)

    def test_wrong_exact_checkout_rejects(self):
        self.env["GITHUB_SHA"] = "0" * 40
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_missing_marker_rejects(self):
        self.path.unlink()
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_tampered_source_checksum_rejects(self):
        data = json.loads(self.path.read_text())
        data["input_manifest_sha256"] = "0" * 64
        self.path.write_text(json.dumps(data))
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_tampered_schema_rejects(self):
        data = json.loads(self.path.read_text())
        data["schema"] = "older-schema"
        self.path.write_text(json.dumps(data))
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_other_repository_rejects(self):
        self.env["GITHUB_REPOSITORY"] = "other/repo"
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_other_platform_rejects(self):
        self.env["RUNNER_ARCH"] = "ARM64"
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_missing_platform_rejects(self):
        del self.env["RUNNER_OS"]
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_symlink_marker_rejects(self):
        text = self.path.read_bytes()
        self.path.unlink()
        other = self.root / "outside-marker.json"
        other.write_bytes(text)
        self.path.symlink_to(other)
        with self.assertRaises(ValueError):
            marker.operate("verify", self.root, self.env)

    def test_symlink_cache_directory_rejects(self):
        self.path.unlink()
        self.path.parent.rmdir()
        other = self.root / "other-cache-markers"
        other.mkdir()
        self.path.parent.symlink_to(other)
        with self.assertRaises(ValueError):
            marker.operate("write", self.root, self.env)

    def test_fresh_commit_marker_survives_older_marker_overlay(self):
        original = self.path.read_bytes()
        older = self.path.parent / ("a" * 40 + ".json")
        older.write_text('{"commit":"older"}')
        self.assertEqual(self.path.read_bytes(), original)
        marker.operate("verify", self.root, self.env)

    def test_same_commit_existing_marker_cannot_be_rebound(self):
        data = json.loads(self.path.read_text())
        data["pins"]["lean-toolchain"] = "a" * 64
        self.path.write_text(json.dumps(data))
        with self.assertRaises(ValueError):
            marker.operate("write", self.root, self.env)

    def test_untrusted_filename_is_literal_git_input(self):
        p = self.root / "Fixture;$(printf owned).lean"
        p.write_text("def fixture2 := 0\n")
        self.commit()
        self.env["GITHUB_SHA"] = self.head
        marker.operate("write", self.root, self.env)
        marker.operate("verify", self.root, self.env)
        self.assertFalse((self.root / "owned").exists())

    def test_all_control_and_docbuild_inputs_are_bound(self):
        old = marker.identity(self.root, self.env)["input_manifest_sha256"]
        (self.root / "docbuild" / "extra-control.txt").write_text("new control\n")
        self.commit()
        self.env["GITHUB_SHA"] = self.head
        self.assertNotEqual(marker.identity(self.root, self.env)["input_manifest_sha256"], old)

    def test_no_build_success_is_inferred_from_marker(self):
        result = marker.operate("verify", self.root, self.env)
        self.assertFalse(result["proof_acceptance"])
        for status in ("failure", "cancelled", "skipped", "", None):
            with self.subTest(status=status), self.assertRaises(ValueError):
                marker.operate("require-success", self.root, {"LEAN_BUILD_RESULT": status})
        self.assertEqual(marker.operate("require-success", self.root,
                         {"LEAN_BUILD_RESULT": "success"})["status"], "upstream-build-success")

    def test_cli_and_optimized_python_reject_tampering(self):
        data = json.loads(self.path.read_text())
        data["input_count"] += 1
        self.path.write_text(json.dumps(data))
        for options in ([], ["-O"], ["-OO"]):
            env = dict(os.environ, **self.env)
            run = subprocess.run([sys.executable, *options, str(SCRIPT), "verify", "--repo", str(self.root)],
                                 env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn(b"cache provenance guard failed", run.stderr)


class WorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = (SCRIPT.parent.parent / ".github/workflows/ci.yml").read_text()

    def block(self, name):
        found = re.search(r"(?ms)^  " + name + r":\n.*?(?=^  [a-zA-Z0-9_-]+:|\Z)", self.text)
        self.assertIsNotNone(found)
        return found.group(0)

    def test_consumers_wait_for_the_build(self):
        for name in ("docs", "comparator"):
            self.assertIn("needs: [source-changes, build]", self.block(name))

    def test_consumers_fail_before_setup_when_build_did_not_succeed(self):
        for name in ("docs", "comparator"):
            block = self.block(name)
            self.assertIn("LEAN_BUILD_RESULT: ${{ needs.build.result }}", block)
            self.assertLess(block.index("ci-build-cache-marker.py require-success"),
                            block.index("leanprover/lean-action@"))

    def test_only_build_writes_marker_before_cache_restore_and_build(self):
        block = self.block("build")
        self.assertLess(block.index("ci-build-cache-marker.py write"),
                        block.index("leanprover/lean-action@"))
        self.assertEqual(self.text.count("ci-build-cache-marker.py write"), 1)
        self.assertEqual(self.text.count("build: true"), 1)

    def test_consumers_verify_after_setup_before_current_output_and_real_checks(self):
        for name, command in (("docs", "lake build PartialBalayage:docs"),
                              ("comparator", "./scripts/verify-comparator.sh")):
            block = self.block(name)
            self.assertLess(block.index("build: false"), block.index("ci-build-cache-marker.py verify"))
            self.assertLess(block.index("ci-build-cache-marker.py verify"), block.index("lake --no-build"))
            self.assertLess(block.index("lake --no-build"), block.index(command))

    def test_exact_fail_closed_outputs_and_original_commands(self):
        self.assertIn("run: lake --no-build build PartialBalayage\n", self.block("docs"))
        self.assertIn("run: lake --no-build build Challenge Solution\n", self.block("comparator"))
        self.assertEqual(self.text.count("run: ./scripts/verify-comparator.sh"), 1)
        self.assertEqual(self.text.count("run: lake build PartialBalayage:docs"), 1)
        self.assertEqual(self.text.count("leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9"), 3)

    def test_existing_classifier_gates_and_timeouts_are_preserved(self):
        condition = "if: ${{ always() && (needs['source-changes'].result != 'success' || needs['source-changes'].outputs.heavy != 'false') }}"
        for name in ("build", "docs", "comparator"):
            self.assertIn(condition, self.block(name))
            self.assertIn("timeout-minutes: 350", self.block(name))


if __name__ == "__main__":
    unittest.main(verbosity=2)
