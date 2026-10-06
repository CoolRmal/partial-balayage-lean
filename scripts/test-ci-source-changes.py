#!/usr/bin/env python3
"""Exercise CI classification with real temporary Git commits, without proof builds."""
import argparse
import ast
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace

SCRIPT = Path(__file__).resolve().with_name("ci-source-changes.py")
spec = importlib.util.spec_from_file_location("ci_source_changes", SCRIPT)
classifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(classifier)


def command(root, *args):
    return subprocess.check_output(["git", "-c", "core.hooksPath=/dev/null", "-C", str(root), *args],
                                   stderr=subprocess.PIPE).decode().strip()


def write(root, path, value):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(value)


def commit(root, message):
    command(root, "add", "--all")
    command(root, "commit", "-q", "--no-gpg-sign", "-m", message)
    return command(root, "rev-parse", "HEAD")


def tests():
    results = []
    with tempfile.TemporaryDirectory(prefix="ci-source-change-git-fixtures-") as tmp:
        root = Path(tmp) / "repository"
        root.mkdir()
        command(root, "init", "-q", "-b", "main")
        command(root, "config", "user.name", "CI classification fixture")
        command(root, "config", "user.email", "ci-test@example.invalid")
        command(root, "config", "commit.gpgsign", "false")
        for path, value in {"README.md": "initial docs\n", "Main.lean": "def fixture := 0\n",
                            "lean-toolchain": "fixture pinned Lean\n",
                            "lakefile.toml": "name = 'fixture'\n",
                            "lake-manifest.json": "{}\n", "comparator.json": "{}\n",
                            ".github/workflows/ci.yml": "initial fixture workflow\n"}.items():
            write(root, path, value)
        initial = commit(root, "initial fixture")

        def check(name, expected, event, checkout, event_name="push", changed=None):
            result = classifier.classify(root, event_name, event, checkout)
            assert result["heavy"] is expected, (name, result)
            if changed is not None:
                assert result["changed_files"] == changed, (name, result)
            results.append({"name": name, "status": "pass", "heavy": result["heavy"],
                            "reason": result["reason"]})
            return result

        changed_cases = [
            ("readme_only_skips_heavy", "README.md", False),
            ("historical_verification_doc_skips_heavy", "docs/VERIFICATION.md", False),
            ("formalization_metadata_only_skips_heavy", "formalization.yaml", False),
            ("new_lean_source_runs_heavy", "PartialBalayage/NewFixture.lean", True),
            ("lean_toolchain_runs_heavy", "lean-toolchain", True),
            ("lake_toml_runs_heavy", "lakefile.toml", True),
            ("lake_lean_runs_heavy", "lakefile.lean", True),
            ("dependency_manifest_runs_heavy", "lake-manifest.json", True),
            ("comparator_configuration_runs_heavy", "comparator.json", True),
            ("verification_script_runs_heavy", "scripts/verify-comparator.sh", True),
            ("classifier_self_change_runs_heavy", "scripts/ci-source-changes.py", True),
            ("docbuild_change_runs_heavy", "docbuild/lakefile.toml", True),
            ("ci_workflow_change_runs_heavy", ".github/workflows/ci.yml", True),
            ("verification_workflow_change_runs_heavy", ".github/workflows/palomar-preflight.yml", True),
            ("composite_action_change_runs_heavy", ".github/actions/fixture/action.yml", True),
            ("untrusted_path_is_literal_data", "docs/path;$(printf owned).md", False),
            ("space_and_unicode_lean_path_runs_heavy", "Fixture space/λ.lean", True),
        ]
        for name, path, expected in changed_cases:
            command(root, "checkout", "--detach", "-q", initial)
            write(root, path, "changed fixture\n")
            head = commit(root, name)
            check(name, expected, {"before": initial, "after": head}, head, changed=[path])
            assert not (root / "owned").exists()

        command(root, "checkout", "--detach", "-q", initial)
        (root / "Main.lean").unlink()
        head = commit(root, "delete actual Lean source")
        check("deleted_lean_source_runs_heavy", True, {"before": initial, "after": head},
              head, changed=["Main.lean"])
        command(root, "checkout", "--detach", "-q", initial)
        (root / "Main.lean").rename(root / "former-source.txt")
        head = commit(root, "rename actual Lean source")
        check("renamed_lean_source_runs_heavy", True, {"before": initial, "after": head},
              head, changed=["Main.lean", "former-source.txt"])

        command(root, "checkout", "--detach", "-q", initial)
        check("empty_exact_diff_skips_heavy", False, {"before": initial, "after": initial},
              initial, changed=[])
        command(root, "commit", "-q", "--allow-empty", "--no-gpg-sign", "-m", "actual empty commit")
        empty_commit = command(root, "rev-parse", "HEAD")
        assert empty_commit != initial
        check("distinct_empty_commit_skips_heavy", False,
              {"before": initial, "after": empty_commit}, empty_commit, changed=[])
        command(root, "checkout", "--detach", "-q", initial)
        check("manual_dispatch_always_runs_heavy", True, {}, initial, "workflow_dispatch")
        check("missing_push_base_runs_heavy", True, {"after": initial}, initial)
        check("new_branch_zero_base_runs_heavy", True, {"before": "0" * 40, "after": initial}, initial)
        check("unavailable_push_base_runs_heavy", True,
              {"before": "1" * 40, "after": initial}, initial)
        check("invalid_ref_is_not_shell_code", True,
              {"before": "$(touch owned)", "after": initial}, initial)
        check("wrong_push_head_runs_heavy", True,
              {"before": initial, "after": "1" * 40}, initial)
        check("wrong_tested_checkout_runs_heavy", True,
              {"before": initial, "after": initial}, "1" * 40)
        check("unknown_event_runs_heavy", True, {}, initial, "unknown_event")
        assert not (root / "owned").exists()

        # Real two-parent PR merges: compare the exact target parent to the tested merge.
        for path, expected in [("docs/pr-only.md", False), ("PRFixture.lean", True)]:
            command(root, "checkout", "--detach", "-q", initial)
            write(root, path, "PR fixture\n")
            head = commit(root, "PR head " + path)
            command(root, "checkout", "--detach", "-q", initial)
            write(root, "BaseFixture.lean", "base source already on target\n")
            base = commit(root, "PR target advanced")
            command(root, "merge", "-q", "--no-ff", "--no-gpg-sign", "-m", "tested PR merge", head)
            merge = command(root, "rev-parse", "HEAD")
            event = {"pull_request": {"base": {"sha": base}, "head": {"sha": head}}}
            check("exact_pr_merge_" + ("proof_runs_heavy" if expected else "docs_skip_heavy"),
                  expected, event, merge, "pull_request", changed=[path])
            check("pr_merge_wrong_parent_runs_heavy", True,
                  {"pull_request": {"base": {"sha": initial}, "head": {"sha": head}}},
                  merge, "pull_request")
            command(root, "checkout", "--detach", "-q", head)
            check("exact_pr_head_checkout_" + ("proof_runs_heavy" if expected else "docs_skip_heavy"),
                  expected, event, head, "pull_request", changed=[path])
        command(root, "checkout", "--detach", "-q", initial)
        check("missing_pr_base_runs_heavy", True,
              {"pull_request": {"head": {"sha": initial}}}, initial, "pull_request")

        # Exercise the executable path, including GitHub output and unavailable event data.
        event = Path(tmp) / "event.json"
        event.write_text(json.dumps({"before": initial, "after": initial}))
        report, github_output = Path(tmp) / "report.json", Path(tmp) / "github-output"
        secret = "DO_NOT_LOG_CREDENTIAL_CI_FIXTURE"
        env = dict(os.environ, GITHUB_OUTPUT=str(github_output), GITHUB_TOKEN=secret)
        output = subprocess.check_output([sys.executable, str(SCRIPT), "--repo", str(root),
            "--event-file", str(event), "--event-name", "push", "--checkout-sha", initial,
            "--output", str(report)], env=env).decode()
        assert json.loads(report.read_text())["heavy"] is False
        assert github_output.read_text() == "heavy=false\n" and secret not in output
        results.append({"name": "actual_cli_outputs_false_without_credentials", "status": "pass"})
        event.unlink()
        output = subprocess.check_output([sys.executable, str(SCRIPT), "--repo", str(root),
            "--event-file", str(event), "--event-name", "push", "--checkout-sha", initial,
            "--output", str(report)], env=env).decode()
        assert json.loads(report.read_text())["heavy"] is True
        assert github_output.read_text().endswith("heavy=true\n") and secret not in output
        results.append({"name": "actual_cli_missing_event_fails_closed", "status": "pass"})
    return {"status": "real_temporary_git_fixture_tests_pass", "cases": results,
            "proof_commands_executed": 0, "network_commands_executed": 0}


def condition_tests(workflow):
    """Evaluate the three actual, strictly validated GitHub conditions on job outcomes."""
    source = workflow.read_text()
    expected = ("${{ always() && (needs['source-changes'].result != 'success' || "
                "needs['source-changes'].outputs.heavy != 'false') }}")
    conditions = {}
    for job in ["build", "docs", "comparator"]:
        block = re.search(r"(?ms)^  " + job + r":\n(.*?)(?=^  [\w-]+:\n|\Z)", source)
        assert block is not None, job
        found = re.findall(r"(?m)^    if: (.+)$", block.group(1))
        assert found == [expected], (job, found)
        expression = found[0][3:-2].strip().replace("&&", "and").replace("||", "or")
        conditions[job] = compile(ast.parse(expression, mode="eval"), str(workflow) + ":" + job, "eval")
    cases = [("successful_docs_only_skips", "success", "false", False),
             ("successful_source_change_runs", "success", "true", True),
             ("successful_missing_output_runs", "success", None, True),
             ("failed_upload_with_false_runs", "failure", "false", True),
             ("cancelled_job_with_false_runs", "cancelled", "false", True),
             ("skipped_job_with_false_runs", "skipped", "false", True),
             ("failed_job_without_output_runs", "failure", None, True),
             ("cancelled_job_without_output_runs", "cancelled", None, True),
             ("unknown_job_result_with_false_runs", None, "false", True)]
    results = []
    for label, status, output, wanted in cases:
        needs = {"source-changes": SimpleNamespace(result=status,
                  outputs=SimpleNamespace(heavy=output))}
        for job, code in conditions.items():
            got = eval(code, {"__builtins__": {}, "always": lambda: True, "needs": needs})
            assert got is wanted, (job, label, got)
            results.append({"job": job, "name": label, "status": "pass", "heavy_runs": got})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--workflow", type=Path,
                        default=Path(__file__).resolve().parents[1] / ".github/workflows/ci.yml")
    args = parser.parse_args()
    report = tests()
    report["workflow_condition_cases"] = condition_tests(args.workflow)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "tests": len(report["cases"]),
                      "workflow_condition_tests": len(report["workflow_condition_cases"])}))


if __name__ == "__main__":
    main()
