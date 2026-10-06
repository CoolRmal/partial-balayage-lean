# Two partial balayage principles in Lean

[![CI](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml)

A candidate Lean formalization of all sixteen upper-bound rows in Yongxi Lin's
[published table](https://coolrmal.github.io/articles/two-partial-balayage-principles/).
The results include complex-input full-vector Riesz and Beurling transforms,
full and traceless Frobenius Hessians, both projections, centred intervals,
Euclidean balls, the strict planar square bound below 3.616, and all six Poisson
and heat bounds. Every maximal estimate covers all integrable real inputs and
all extended-real levels. The semigroup bounds use exact formulas and proved
unique parameters.

The comparator is configured for all sixteen statements. The four new square
assembly modules and ten imported axiom audits have passed focused local checks.
Full sixteen-row ordinary CI and unchanged cold official verification remain
pending, and the repository is **not registered on
Palomar**. The earlier fifteen-row snapshot
`e301f763ae0c819976384ea733f7327e80ce1c44`, including full complex-input Riesz,
[passed official full Palomar preflight](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37404883784)
with no errors or warnings. Comparator and Lean, NanoDa and con-ron accepted
that earlier solution. The final sixteen-row snapshot still requires the
complete official check. Exact scope, evidence and earlier failed attempts
are recorded in [docs/VERIFICATION.md](docs/VERIFICATION.md).

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
statements use the independently defined concrete Fourier operators. Actual signed
Poisson balayage, full-norm Fourier regularity and physical Sobolev zero-set locality
give the full-vector Riesz coefficient two on every real L¹ input.
The complex extension constructs a genuine complex norm-capped Poisson
decomposition, proves physical Poisson regularization, the full frequency-norm
identity and actual self-energy pairing, and identifies every Riesz coordinate
with a physical first derivative. Real and imaginary zero-set locality give
full-vector cancellation. Its norm-capped level-set estimate and genuine complex
linear L¹ extension prove the complete complex-input table theorem.

The square proof constructs the actual nonnegative kernel and proves its
closed-diamond majorization and exact mass bound. The original radial and
cubic-spline sources are identified through genuine punctured test identities,
with the full even compensated source representation and required second
moment. Exact Taylor enclosures and incoming-tail estimates, the complete
subdivision and floor-based coverage proof, and all 106 checked numerical
blocks prove positivity of the actual interior generator. Boundary and axis
identities give the almost-everywhere nonnegative source used by the source
comparison theorem. Genuine mollification, source convolution and the closed
full-source graph transfer the constructed state to that singular source.
Physical diamond averages, all positive radii, every extended-real level and
monotone L¹ truncations transfer the coefficient to the original square
operator, proving

$$
c(M_\square)<\frac{452}{125}=3.616.
$$

[All 106 numerical blocks and the combined audit passed on Linux](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37409981058).
The exact split registry then compiled locally in 56.237 seconds and its three
imported axiom audits completed in 7.415 seconds. Rectangle alignment uses 106
separate checks of 64 labels, preserving the original registry data and public
theorem statements. The remaining three assembly modules also compiled locally,
and all ten imported theorem audits use only `propext`, `Classical.choice` and
`Quot.sound`. The resulting square theorem has no positivity or numerical
certificate premise.

The earlier integration attempts 37422022840 and 37431956910 failed during
assembly and remain recorded as failures. The latter saved the completed
713-module support checkpoint before assembly. These focused local results
do not turn either failed run into a pass. Complete sixteen-row ordinary CI,
unchanged cold official verification and Palomar registration remain pending.

Some table decimals approximate exact formulas and are not rigorous truncated upper
bounds. The formal statements retain exact expressions. The square target is strictly
below 3.616; the earlier bound 3.879 does not meet it.

## Project map

- `Challenge.lean`: sixteen independent auditable statements importing Mathlib alone.
- `Solution.lean`: the matching proved declarations.
- `PartialBalayage/`: new proofs and adapters to earlier results.
- `CenteredMaximal/`: the copied minimal earlier source closure, preserving author headers.
- `comparator.json`: the exact sixteen statements compared.
- `formalization.yaml`: provenance, scope, automation and review metadata.
- `docs/DECOMPOSITION.md`: all sixteen targets and the proof dependencies.
- `docs/PALOMAR.md`: verification and eventual registration procedure.

Lean and Mathlib are pinned; committed manifests record exact dependency revisions.
Build with `lake exe cache get` followed by `lake build`. The deliberate Challenge
holes state the problems and do not enter Solution. Linux CI runs the pinned
Comparator with its bundled NanoDa and con-ron independent kernels. Official Palomar
full preflight verifies an immutable public snapshot; a build alone is not a
Comparator pass.

After the complete sixteen-row snapshot passes official verification, it will be submitted
through [Palomar's intake](https://submit.palomar-registry.org/). Final registration
requires review and the human author's consent to that exact review.

## Provenance and licence

Mathematics and human authorship: Yongxi Lin. Codex and its collaborating agents
assist with formalization and verification; no AI system is listed as an author.
The template comes from [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406).
Code is Apache-2.0. No external human review has been obtained.
