#!/usr/bin/env python3
"""Control tooling: apply only inside the gated isolated Ubuntu job.

This tool never runs Lean or alters the actual numerical records.  The workflow must first restore and audit the
already successful remote source candidate using its frozen control revision.
"""
import argparse
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

CANDIDATE = "dde634e918bcbba00881018b205dea4172d2ee5f"
CONTROL = "243a5bd4f80c9517e7c9f834e85c5154eeb8e9a9"
RUN = 37409981058
PREFIX = "PartialBalayage.Maximal.Square.Data.GeneratorLeafBlocks"
FINAL = [
    "PartialBalayage.Maximal.Square.GeneratorLeafBlocks",
    "PartialBalayage.Maximal.Square.GeneratorInteriorPositivity",
    "PartialBalayage.Maximal.Square.SquarePositiveSource",
    "PartialBalayage.Maximal.SquareWeakBounds",
]
FINAL_SHA256 = {
    FINAL[0]: "be7c5f5dfb0aaba5d18bba4a8e67507ce90d259198913b6713e438528fc10fd5",
    FINAL[1]: "ec2fdcc627be8a4ec0efd21a41d2492fd64953d330f7f1b2e739a7e76ee357f1",
    FINAL[2]: "86aacc42a8d7d317b6e4e12da71c1dfd4dded0ace15a426ddfc4673a8a8ebfe9",
    FINAL[3]: "99da5c7d3e0f0bd20ba893f31f029cdc34d60aa964ca751208211ecac1888b65",
}
ROOT = Path.cwd()
IMPORT = re.compile(r"^(?:(?:public|meta)\s+)*import\s+([^\n]+)", re.MULTILINE)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def source(commit, path):
    return git("show", f"{commit}:{path}")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def records(data, block):
    pattern = rb"(?ms)^def generatorLeafBlocks" + str(block).encode() + rb"\b.*?^\]\s*$"
    match = re.search(pattern, data)
    require(match is not None, f"Missing actual record definition in block {block}")
    return match.group()


def closure():
    paths = git("ls-tree", "-r", "--name-only", CANDIDATE).decode().splitlines()
    internal = {p[:-5].replace("/", "."): p for p in paths if p.endswith(".lean")}
    queue = deque(PREFIX + str(b) for b in range(106))
    result = {}
    while queue:
        module = queue.popleft()
        if module in result:
            continue
        path = internal[module]
        data = source(CANDIDATE, path)
        imports = []
        for line in IMPORT.findall(data.decode()):
            imports.extend(m for m in line.split("--", 1)[0].split() if m in internal)
        result[module] = {"path": path, "sha256": sha(data), "imports": sorted(set(imports))}
        queue.extend(imports)
    require(len(result) == 346, "Unexpected numerical transitive source closure")
    return result


def reviewed_final_sources(commit, paths):
    result = {}
    for module in FINAL:
        path = module.replace(".", "/") + ".lean"
        require(path in paths, f"Commit the reviewed final draft before integration: {path}")
        actual = sha(source(commit, path))
        require(actual == FINAL_SHA256[module], f"Unreviewed final draft source: {path}")
        result[module] = actual
    return result


def support_plan(commit, paths, numeric):
    """Derive a root-inclusive import DAG; support never depends on a leaf or assembly."""
    internal = {p[:-5].replace("/", "."): p for p in paths if p.endswith(".lean")}
    internal.update({module: item["path"] for module, item in numeric.items()})
    graph, active, ordered = {}, set(), []

    def visit(module):
        require(module not in active, f"Cyclic project imports at {module}")
        if module in graph:
            return
        require(module in internal, f"Missing project import: {module}")
        active.add(module)
        path = internal[module]
        origin = CANDIDATE if module in numeric else commit
        data = source(origin, path)
        imports = set()
        for line in IMPORT.findall(data.decode()):
            for item in line.split("--", 1)[0].split():
                if item in internal:
                    imports.add(item)
                elif item.startswith(("PartialBalayage.", "CenteredMaximal.")):
                    require(False, f"Missing project import: {item} in {module}")
        for dependency in sorted(imports):
            visit(dependency)
        active.remove(module)
        graph[module] = {"path": path, "sha256": sha(data), "imports": sorted(imports),
                         "source_commit": origin}
        ordered.append(module)

    for module in FINAL:
        visit(module)
    leaf_modules = {PREFIX + str(b) for b in range(106)}
    forbidden = leaf_modules | set(FINAL)
    support = [module for module in ordered if module not in numeric and module not in FINAL]
    ancestors = {}
    for module in ordered:
        transitive = set(graph[module]["imports"])
        for dependency in graph[module]["imports"]:
            transitive.update(ancestors[dependency])
        ancestors[module] = transitive
        if module in support:
            require(not (transitive & forbidden),
                    f"Support module depends on numerical leaf or final assembly: {module}")
    available = set(numeric)
    for module in support:
        require(set(graph[module]["imports"]) <= available,
                f"Unprepared support dependencies: {module}")
        available.add(module)
    for module in FINAL:
        require(set(graph[module]["imports"]) <= available,
                f"Final assembly order has unprepared imports: {module}")
        available.add(module)
    return {"graph": graph, "support_modules": support,
            "root_inclusive_project_module_count": len(graph),
            "numeric_module_count": len(numeric), "support_module_count": len(support),
            "final_assembly_count": len(FINAL), "roots": FINAL,
            "numeric_intersection_count": len(set(graph) & set(numeric))}


def protected_leaf_outputs(outputs):
    pattern = re.compile(r"^\.lake/build/(?:lib/lean|ir)/PartialBalayage/Maximal/Square/"
                         r"Data/GeneratorLeafBlocks(\d+)\.")
    result = {path: item for path, item in outputs.items() if pattern.match(path)}
    suffixes = [".olean", ".olean.private", ".olean.server", ".ilean", ".trace",
                ".olean.hash", ".olean.private.hash", ".olean.server.hash", ".ilean.hash"]
    for block in range(106):
        stem = ".lake/build/lib/lean/" + (PREFIX + str(block)).replace(".", "/")
        for suffix in suffixes:
            require(stem + suffix in result, f"Missing restored leaf output: {stem + suffix}")
    require(all(0 <= int(pattern.match(path).group(1)) < 106 for path in result),
            "Unexpected restored numerical block output")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--integration-commit", required=True)
    parser.add_argument("--run-metadata", type=Path, required=True)
    parser.add_argument("--apply-after-full-pass", action="store_true")
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{40}", args.integration_commit),
            "Integration commit must be an exact full public SHA")
    run = json.loads(args.run_metadata.read_text())
    require(run["id"] == RUN and run["head_sha"] == CONTROL,
            "Wrong numerical run or dispatcher revision")
    require(run["status"] == "completed" and run["conclusion"] == "success",
            "The entire numerical source run has not passed")
    require(git("rev-parse", "HEAD").decode().strip() == CANDIDATE,
            "Restore first in the exact source candidate checkout")
    output_dir = Path(os.environ["RUNNER_TEMP"]) / "square-numerical"
    restored = json.loads((output_dir / "aggregate-outputs-report.json").read_text())
    require(restored["status"] == "restored", "All genuine numerical outputs must be restored")
    require(restored["snapshot"]["commit"] == CANDIDATE and
            restored["control_commit"] == CONTROL, "Restored output provenance differs")
    for path, value in restored["snapshot"]["source_hashes"].items():
        require(sha((ROOT / path).read_bytes()) == value, f"Restored source changed: {path}")
    for path, value in restored["outputs"].items():
        require(sha((ROOT / path).read_bytes()) == value["sha256"],
                f"Restored output changed: {path}")
    dependencies = closure()
    leaf_modules = {PREFIX + str(b) for b in range(106)}
    integration_paths = set(git("ls-tree", "-r", "--name-only", args.integration_commit)
                            .decode().splitlines())
    for prefix in (".square-control/", ".integration-control/", ".lake/"):
        require(not any(p.startswith(prefix) for p in integration_paths),
                "Integration commit tracks a reserved build/control directory")
    for path in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        require(source(CANDIDATE, path) == source(args.integration_commit, path),
                f"Integration changed a dependency pin or build option: {path}")
    for module, item in dependencies.items():
        if module not in leaf_modules:
            require(source(args.integration_commit, item["path"]) ==
                    source(CANDIDATE, item["path"]),
                    f"Integration changed an actual numerical dependency: {module}")
    transition = []
    for block in range(106):
        path = (PREFIX + str(block)).replace(".", "/") + ".lean"
        candidate = source(CANDIDATE, path)
        before = source(args.integration_commit, path) if path in integration_paths else None
        if before is not None:
            require(records(before, block) == records(candidate, block),
                    f"Integration changed actual numerical records in block {block}")
        transition.append({"block": block, "path": path, "sha256": sha(candidate),
                           "records_sha256": sha(records(candidate, block)),
                           "already_in_integration_commit": before is not None})
    final_sources = reviewed_final_sources(args.integration_commit, integration_paths)
    preparation = support_plan(args.integration_commit, integration_paths, dependencies)
    leaf_outputs = protected_leaf_outputs(restored["outputs"])
    if args.apply_after_full_pass:
        subprocess.run(["git", "checkout", "--detach", args.integration_commit],
                       cwd=ROOT, check=True)
        for item in transition:
            path = ROOT / item["path"]
            path.parent.mkdir(parents=True, exist_ok=True)
            require(not path.is_symlink(), f"Nonregular source destination: {path}")
            path.write_bytes(source(CANDIDATE, item["path"]))
        for module, item in dependencies.items():
            require(sha((ROOT / item["path"]).read_bytes()) == item["sha256"],
                    f"Numerical source closure differs after transition: {module}")
        for module, item in preparation["graph"].items():
            require(sha((ROOT / item["path"]).read_bytes()) == item["sha256"],
                    f"Integration import source differs after transition: {module}")
    report = {"status": "applied" if args.apply_after_full_pass else "checked-only",
              "numerical_run": RUN, "candidate": CANDIDATE, "control": CONTROL,
              "integration_commit": args.integration_commit, "closure": dependencies,
              "transition": transition, "final_modules": FINAL,
              "reviewed_final_source_sha256": final_sources,
              "support_preparation": preparation, "protected_leaf_outputs": leaf_outputs}
    (output_dir / "integration-source-report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"{report['status']}: exact 346-module numerical closure, 106 actual records preserved")


if __name__ == "__main__":
    main()
