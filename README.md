# Two partial balayage principles in Lean

[![CI](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml)

Work in progress toward formalizing all sixteen upper-bound rows in Yongxi Lin's
[published table](https://coolrmal.github.io/articles/two-partial-balayage-principles/).
Fourteen rows are now proved: the complex-input Beurling transform, full and
traceless Frobenius Hessians, both projections, centred intervals, Euclidean balls,
and all six Poisson and heat maximal bounds. Every maximal estimate
quantifies over all integrable real inputs and all extended-real levels. The six new
semigroup bounds use the article's exact formulas and proved unique parameters.

The full-vector real-input Riesz and square rows remain pending. This repository has
**not** completed the table and is **not registered on Palomar**. The comparator is
configured for fourteen statements, and their
[official full Palomar preflight passed](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37359788746).
Exact verified commits, scope and earlier failed attempts are recorded in
[docs/VERIFICATION.md](docs/VERIFICATION.md).

The three interval and Euclidean-ball proofs are adapted from the author's
[earlier formalization](https://github.com/CoolRmal/centered-maximal-constant/tree/72c022ba09032b522c878cca2f9b6c68217d77ea).
Their exact bounds are

$$
c_1\le2,\qquad c_{\mathrm{ball},2}\le e,\qquad
c_{\mathrm{ball},n}\le(n/2)^{n/(n-2)}\quad(n\ge3).
$$

The new semigroup proofs construct actual positive whole-space Laplace balayage,
prove its cap complementarity and active-volume bound, compare the original kernels
with genuine integrable tangent majorants, compute their exact masses, and pass
rational-time comparisons to the full supremum. Monotone L¹ and L² truncations extend
the exact estimates to every integrable input. Parameter existence and uniqueness,
the one-dimensional Gaussian and arctangent tails, and the planar elementary
formulas are proved. The final statements assume no analytical certificates.

Supporting development also constructs actual whole-space vector balayage and proves
genuine global Sobolev regularity and Hessian cancellation. Fourier multipliers use
Euclidean vector and Frobenius matrix norms. Actual complex capped decompositions
and Hessian locality give the Beurling, full and traceless Hessian and projection
bounds. Genuine linear L¹ extensions
are proved to exist and to be unique among finite weak-bound extensions. The final
statements use the independently defined concrete Fourier operators.

Some table decimals approximate exact formulas and are not rigorous truncated upper
bounds. The formal statements retain exact expressions. The square target is strictly
below 3.616; the earlier bound 3.879 does not meet it.

## Project map

- `Challenge.lean`: fourteen independent auditable statements importing Mathlib alone.
- `Solution.lean`: the matching proved declarations.
- `PartialBalayage/`: new proofs and adapters to earlier results.
- `CenteredMaximal/`: the copied minimal earlier source closure, preserving author headers.
- `comparator.json`: the exact fourteen statements currently compared.
- `formalization.yaml`: provenance, scope, automation and review metadata.
- `docs/DECOMPOSITION.md`: all sixteen targets and the proof dependencies.
- `docs/PALOMAR.md`: verification and eventual registration procedure.

Lean and Mathlib are pinned; committed manifests record exact dependency revisions.
Build with `lake exe cache get` followed by `lake build`. The deliberate Challenge
holes state the problems and do not enter Solution. Linux CI runs the pinned
Comparator with its bundled NanoDa and con-ron independent kernels. Official Palomar
full preflight verifies an immutable public snapshot; a build alone is not a
Comparator pass.

After all sixteen rows are proved, the final commit will be verified and submitted
through [Palomar's intake](https://submit.palomar-registry.org/). Final registration
requires review and the human author's consent to that exact review.

## Provenance and licence

Mathematics and human authorship: Yongxi Lin. Codex and its collaborating agents
assist with formalization and verification; no AI system is listed as an author.
The template comes from [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406).
Code is Apache-2.0. No external human review has been obtained.
