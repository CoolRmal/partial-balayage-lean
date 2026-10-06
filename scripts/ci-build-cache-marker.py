#!/usr/bin/env python3
"""Bind ordinary CI's cached .lake to exact inputs; this is not a proof receipt."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

SCHEMA = "ordinary-ci-inputs-v1"
PINS = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json",
        "docbuild/lean-toolchain", "docbuild/lakefile.toml", "docbuild/lake-manifest.json")


def git(root, *args):
    return subprocess.check_output(["git", "--no-optional-locks", "-C", str(root), *args],
                                   stderr=subprocess.PIPE)


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def require_regular(root, relative):
    path = root / relative
    current = root
    for part in Path(relative).parts:
        current /= part
        if current.is_symlink():
            raise ValueError("symbolic link is not a cache provenance input: " + relative)
    if not path.is_file():
        raise ValueError("missing regular cache provenance input: " + relative)
    return path


def identity(root, env):
    root = root.resolve()
    head = git(root, "rev-parse", "--verify", "HEAD").decode().strip()
    expected = env.get("GITHUB_SHA", "")
    if re.fullmatch(r"[0-9a-f]{40}", expected) is None or head != expected:
        raise ValueError("checkout is not the exact CI commit")
    if git(root, "status", "--porcelain", "--untracked-files=no"):
        raise ValueError("tracked checkout is dirty")
    context = {key: env.get(key, "") for key in ("GITHUB_REPOSITORY", "RUNNER_OS", "RUNNER_ARCH")}
    if not all(context.values()):
        raise ValueError("missing CI repository/platform identity")
    tracked = [os.fsdecode(p) for p in git(root, "ls-files", "-z").split(b"\0") if p]
    inputs = sorted(p for p in tracked if p.endswith(".lean") or p in PINS or
                    p.startswith(("scripts/", "docbuild/")) or p == ".github/workflows/ci.yml")
    if not all(pin in inputs for pin in PINS) or not any(p.endswith(".lean") for p in inputs):
        raise ValueError("missing tracked source/dependency inputs")
    source_rows = [{"path": p, "sha256": digest(require_regular(root, p))} for p in inputs]
    encoded = json.dumps(source_rows, sort_keys=True, separators=(",", ":")).encode()
    return {"schema": SCHEMA, "commit": head, "context": context,
            "input_manifest_sha256": hashlib.sha256(encoded).hexdigest(),
            "input_count": len(inputs), "lean_source_count": sum(p.endswith(".lean") for p in inputs),
            "pins": {p: digest(require_regular(root, p)) for p in PINS},
            "meaning": "exact build inputs only; successful upstream build and Lake current-output checks required"}


def marker_path(root, commit, create=False):
    directory = root / ".lake" / "ci-inputs-v1"
    current = root
    for part in (".lake", "ci-inputs-v1"):
        current /= part
        if current.is_symlink() or (current.exists() and not current.is_dir()):
            raise ValueError("cache marker parent is not an ordinary directory")
    if create:
        directory.mkdir(parents=True, exist_ok=True)
    path = directory / (commit + ".json")
    if path.is_symlink():
        raise ValueError("cache marker is a symbolic link")
    return path


def operate(mode, root, env):
    if mode == "require-success":
        if env.get("LEAN_BUILD_RESULT") != "success":
            raise ValueError("the current upstream Lean build did not succeed")
        return {"status": "upstream-build-success", "proof_acceptance": False}
    root = root.resolve()
    expected = identity(root, env)
    path = marker_path(root, expected["commit"], create=mode == "write")
    if mode == "write":
        if path.exists() and json.loads(path.read_text()) != expected:
            raise ValueError("existing same-commit marker has different inputs")
        path.write_text(json.dumps(expected, sort_keys=True, indent=2) + "\n")
    elif mode == "verify":
        if not path.is_file() or json.loads(path.read_text()) != expected:
            raise ValueError("cached build-input marker is missing or does not match this checkout")
    else:
        raise ValueError("unknown marker operation")
    return {"status": "exact-inputs-match", "marker": str(path), "commit": expected["commit"],
            "input_manifest_sha256": expected["input_manifest_sha256"], "proof_acceptance": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("write", "verify", "require-success"))
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    args = parser.parse_args()
    try:
        result = operate(args.mode, args.repo, os.environ)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, "cache provenance guard failed: " + str(error) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
