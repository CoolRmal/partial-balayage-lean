# Verification evidence

## First three-row milestone

Commit: `e500723e7c7becd4f14c44118bb821778c12cfb6`.

The [GitHub comparator job](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37304016839/job/111743213448)
completed successfully on 5 October 2026. It runs the pinned Lean toolchain's
`lake comparator`, with its bundled NanoDa and con-ron independent kernel checkers.
The compared statements are exactly the three names in `comparator.json`:
centred intervals, planar Euclidean balls, and higher-dimensional Euclidean balls.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

The same commit's build, source checks and metadata/licence checks passed.
The local full Lean build also passed. Local axiom inspections of the three
adapters reported exactly the standard three axioms.

This evidence does not prove the other thirteen article rows. Palomar registration
has not occurred. A final full preflight and review must use the final immutable
commit after those rows are completed.

The first official mechanical-preflight attempt failed during intake, before Lean was checked.
The pinned verifier requires a twelve-character lowercase alphanumeric request ID and the
authorization relationship in its options. Both workflow inputs have been corrected. The
verifier's reporting step masked these intake errors as a malformed-report error; neither that
attempt nor successful parsing of the corrected inputs is evidence of a full preflight pass.

## Second proof checkpoint

Commit: `897dd0ad93bfe8e78b25159feaafad2b2a3571b5`.

The corrected [official full preflight](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37306182443)
completed successfully. Its mechanical report has `status: pass`, `stage: complete`,
`phase: verification`, no errors and no warnings, and identifies this exact repository and
commit. It checks the same three theorem names above, under `palomar-standard-v1` with
the pinned pipeline revision recorded in the workflow. The report is mechanical evidence
for this checkpoint, not registration or completion of the other table rows.
