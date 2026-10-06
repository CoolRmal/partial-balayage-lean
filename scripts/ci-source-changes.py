#!/usr/bin/env python3
"""Classify exact CI source differences. Unavailable or ambiguous inputs run heavy checks."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

SHA = re.compile(r"[0-9a-f]{40}")
CONFIGS = {"lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json",
           "comparator.json"}


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], stderr=subprocess.PIPE)


def exact_sha(value):
    return isinstance(value, str) and SHA.fullmatch(value) is not None and value != "0" * 40


def category(path):
    if path.endswith(".lean"):
        return "Lean source"
    if path.rsplit("/", 1)[-1] in CONFIGS:
        return "dependency or comparator configuration"
    if path.startswith("scripts/"):
        return "verification or control script"
    if path.startswith("docbuild/"):
        return "documentation build input"
    if path.startswith((".github/workflows/", ".github/actions/")):
        return "CI workflow or action"
    return None


def classify(repo, event_name, event, checkout_sha):
    result = {"event": event_name, "heavy": True, "reason": "unresolved exact source difference",
              "base_sha": None, "head_sha": None, "tested_sha": None, "changed_files": []}

    def force(reason):
        result["reason"] = reason
        return result

    if event_name == "workflow_dispatch":
        return force("manual dispatch always runs heavy checks")
    if event_name not in ["push", "pull_request"]:
        return force("unsupported event requires heavy checks")
    if not exact_sha(checkout_sha):
        return force("missing or invalid exact tested commit")
    try:
        actual = git(repo, "rev-parse", "--verify", "HEAD").decode().strip()
        if actual != checkout_sha:
            return force("checkout does not match the exact tested commit")
        if event_name == "push":
            base, head = event.get("before"), event.get("after")
            if not exact_sha(base):
                return force("missing exact push base")
            if not exact_sha(head) or head != checkout_sha:
                return force("push head does not match the exact tested commit")
        else:
            pull = event.get("pull_request", {})
            base = pull.get("base", {}).get("sha")
            head = pull.get("head", {}).get("sha")
            if not exact_sha(base) or not exact_sha(head):
                return force("missing exact pull request base or head")
        result.update(base_sha=base, head_sha=head, tested_sha=checkout_sha)
        for sha in {base, head, checkout_sha}:
            git(repo, "cat-file", "-e", sha + "^{commit}")
        comparison_base = base
        if event_name == "pull_request":
            if checkout_sha == head:
                comparison_base = git(repo, "merge-base", base, head).decode().strip()
                if not exact_sha(comparison_base):
                    return force("no exact pull request merge base")
            else:
                parents = git(repo, "rev-list", "--parents", "-n", "1", checkout_sha).decode().split()
                if len(parents) != 3 or set(parents[1:]) != {base, head}:
                    return force("tested pull request merge does not match exact event parents")
        raw = git(repo, "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
                  "--name-only", "-z", comparison_base, checkout_sha, "--")
        changed = sorted(os.fsdecode(path) for path in raw.split(b"\0") if path)
        relevant = [{"path": path, "category": category(path)}
                    for path in changed if category(path) is not None]
        result.update(heavy=bool(relevant), comparison_base_sha=comparison_base,
                      changed_files=changed, heavy_inputs=relevant,
                      reason="proof or verification inputs changed" if relevant else
                      "exact diff changes no proof or verification inputs")
        return result
    except (subprocess.CalledProcessError, OSError, UnicodeError, AttributeError, TypeError):
        return force("exact Git difference unavailable; heavy checks required")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--event-file", type=Path,
                        default=Path(os.environ.get("GITHUB_EVENT_PATH", "/nonexistent-ci-event")))
    parser.add_argument("--event-name", default=os.environ.get("GITHUB_EVENT_NAME", ""))
    parser.add_argument("--checkout-sha", default=os.environ.get("GITHUB_SHA", ""))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        event = json.loads(args.event_file.read_text())
        if not isinstance(event, dict):
            raise ValueError("Event must be a JSON object")
        result = classify(args.repo, args.event_name, event, args.checkout_sha)
    except (OSError, ValueError):
        result = {"event": args.event_name, "heavy": True,
                  "reason": "event metadata unavailable; heavy checks required", "changed_files": []}
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    if os.environ.get("GITHUB_OUTPUT"):
        with Path(os.environ["GITHUB_OUTPUT"]).open("a") as stream:
            stream.write("heavy=" + str(result["heavy"]).lower() + "\n")
    print(json.dumps(result, ensure_ascii=True))


if __name__ == "__main__":
    main()
