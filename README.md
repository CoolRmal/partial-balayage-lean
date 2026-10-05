# Two partial balayage principles in Lean

[![CI](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml)

Work in progress toward formalizing all sixteen upper-bound rows in Yongxi Lin's
[published table](https://coolrmal.github.io/articles/two-partial-balayage-principles/).
The target includes Riesz and Beurling transforms, Hessians, projections, centred maximal
operators, and Poisson and heat maximal operators.

The initial Challenge/Solution pair covers three rows: centred intervals, planar Euclidean
balls, and Euclidean balls in dimensions at least three. Their proofs are adapted from the
[earlier formalization](https://github.com/CoolRmal/centered-maximal-constant/tree/72c022ba09032b522c878cca2f9b6c68217d77ea).
The other thirteen rows are pending. This repository has **not** completed the table and is
**not registered on Palomar**. A Comparator pass for the current three statements certifies
only those statements.

For an integrable real function, the centred maximal function takes the supremum of averages
of its absolute value over every centred interval or ball. The compared claims are

$$
c_1\le 2,\qquad c_{\mathrm{ball},2}\le e,\qquad
c_{\mathrm{ball},n}\le (n/2)^{n/(n-2)}\quad(n\ge3).
$$

The Challenge uses Lebesgue measure and quantifies over every integrable input and every
level. Balls use the Euclidean norm. Cubes use the sup norm; in dimension one they are intervals.

Some source table entries are decimal approximations to exact formulas. Truncated decimals
are not rigorous upper bounds; formal statements will retain the exact formulas. The new
square target is strictly below 3.616. The earlier bound 3.879 does not meet it.

New supporting proofs establish the level-set estimate from concrete capped decomposition
data and its optimized coefficient, as well as the complex-input Beurling transform's L²
contraction through Mathlib's unitary Fourier transform. The Poisson and heat convolution
maximal operators and their exact parameterized bound formulas are defined, with kernel
positivity and heat-kernel mass one proved. The full vector Riesz and Frobenius-matrix Hessian
operators have L² contraction proofs. Exact scalar optimization yields the Hessian coefficients
and the projection coefficient from its unique cubic root. The radial constants and unique
positive heat parameter are also proved; the sharper prescribed lower endpoint of its interval
remains pending. These steps do not yet prove any of the thirteen pending weak-type rows.

## Project map

- `Challenge.lean`: independent auditable statements importing Mathlib alone.
- `Solution.lean`: matching proved declarations.
- `PartialBalayage/`: new development and adapters to earlier proofs.
- `CenteredMaximal/`: the required copied source closure with author headers preserved.
- `comparator.json`: exact statements currently compared.
- `formalization.yaml`: provenance, scope, automation and review metadata.
- `docs/DECOMPOSITION.md`: complete table and remaining proof dependencies.
- `docs/PALOMAR.md`: verification and eventual registration procedure.

Lean and Mathlib are pinned; committed manifests record exact dependency revisions.
Build with `lake exe cache get` followed by `lake build`. The deliberate Challenge `sorry`
holes state the problem and do not enter the Solution.

Linux CI runs `scripts/verify-comparator.sh` with the toolchain's Comparator and independent
kernels. Manual Palomar preflight verifies a specified immutable commit. A successful build
alone is not a Comparator pass.

After every row is proved, the final commit will be verified and submitted through
[Palomar's intake](https://submit.palomar-registry.org/). Inspect the returned review and exact
claims before registration.

## Provenance and licence

Mathematics and human authorship: Yongxi Lin. Codex and its collaborating agents assist with
formalization and verification; no AI system is listed as an author. Layout and verification
scripts start from [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406).
Code is Apache-2.0. No external human review has been obtained.
