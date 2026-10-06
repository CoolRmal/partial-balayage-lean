# Two partial balayage principles in Lean

[![CI](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/CoolRmal/partial-balayage-lean/actions/workflows/ci.yml)

A Lean formalization of fifteen rows in Yongxi Lin's
[published table](https://coolrmal.github.io/articles/two-partial-balayage-principles/).
The included results cover the full complex-input Riesz and Beurling transforms,
full and traceless Frobenius Hessians, both projections, centred intervals,
Euclidean balls, and all six Poisson and heat bounds. The planar square row is
excluded from the current proof and Comparator scope.

The square bound below $$3.616$$ is difficult to verify because its proof uses
large exact arithmetic certificates. That proof and its numerical development
have been removed from this repository's scope. The weaker bound
$$c(M_\square)\le3.879$$ is formalized in
[centered-maximal-constant](https://github.com/CoolRmal/centered-maximal-constant),
where the actual theorem is
[`CenteredMaximal.weakTypeConstant_two_le_upper`](https://github.com/CoolRmal/centered-maximal-constant/blob/72c022ba09032b522c878cca2f9b6c68217d77ea/Solution.lean#L38).
That separate result does not replace the article's square row here.

## Complete article table and current scope

All sixteen article rows are listed below. “Included” identifies the fifteen
rows in the current source and Comparator; it does not claim that the cleaned
snapshot has already passed a new complete verification run. Write $$c(T)$$ for
the weak-type $$(1,1)$$ constant of $$T$$.

| Row | Operator | Article upper bound | Current scope |
| --- | --- | --- | --- |
| 1 | Riesz transform | $$2$$ | Included |
| 2 | Beurling–Ahlfors transform | $$2$$ | Included |
| 3 | Second-order Riesz transform, $$n=2$$ | $$3\sqrt6/4$$ | Included |
| 4 | Second-order Riesz transform, $$n\ge2$$ | $$1/a_n+(n-1)a_n/(n-a_n^2)$$ | Included |
| 5 | Traceless second-order Riesz transform | $$2\sqrt{1-n^{-1}}$$ | Included |
| 6 | Leray and gradient projections | $$\approx1.805$$ | Included, exact expression |
| 7 | Centred Hardy–Littlewood maximal operator, $$n=1$$ | $$2$$ | Included |
| 8 | Centred maximal operator for Euclidean balls, $$n=2$$ | $$e$$ | Included |
| 9 | Centred maximal operator for axis-parallel squares, $$n=2$$ | $$<3.616$$ | **Excluded** |
| 10 | Centred maximal operator for Euclidean balls, $$n\ge3$$ | $$(n/2)^{n/(n-2)}$$ | Included |
| 11 | Poisson maximal operator, $$n=1$$ | $$1+\frac2\pi\left(\frac{\sqrt5}{3}-\arctan\frac2{\sqrt5}\right)\approx1.010$$ | Included |
| 12 | Poisson maximal operator, $$n=2$$ | $$\approx1.021$$ | Included, exact expression |
| 13 | Poisson maximal operator | $$\frac{\Gamma((n+1)/2)}{\sqrt\pi\,\Gamma(n/2)}\left[\frac{2b_P^{n/2}}{n(1+a_P)^{(n+1)/2}}+\int_{b_P}^\infty\frac{z^{n/2-1}}{(1+z)^{(n+1)/2}}\,dz\right]$$ | Included for $$n\ge1$$ |
| 14 | Heat maximal operator, $$n=1$$ | $$\approx1.037087$$ | Included, exact expression |
| 15 | Heat maximal operator, $$n=2$$ | $$\approx1.094052$$ | Included, exact expression |
| 16 | Heat maximal operator | $$\frac1{\Gamma(n/2)}\left[\frac{2(\rho_n a_H)^{n/2}e^{-a_H}}n+\int_{\rho_n a_H}^\infty z^{n/2-1}e^{-z}\,dz\right]$$ | Included for $$n\ge1$$ |

The parameters follow the article:

$$
a_n=\sqrt{\frac{2n}{n+1+\sqrt{(n+1)^2+4(n-2)}}},\qquad
\rho_n=\begin{cases}(n/2)^{2/(n-2)},&n\ne2,\\e,&n=2.\end{cases}
$$

For Poisson, $$a_P=a_P(n)$$ is the unique solution in
$$(n/(3\rho_n),n/3)$$ of

$$
\frac{1-a_P/n}{(1+a_P)^{(n+3)/2}}
=\frac1{(1+\rho_n a_P)^{(n+1)/2}},\qquad b_P=\rho_n a_P.
$$

For heat, $$a_H=a_H(n)$$ is the unique nonzero solution in
$$(n/(2\rho_n),n/2)$$ of

$$
e^{-(\rho_n-1)a_H}=1-\frac{2a_H}{n}.
$$

The decimal labels are approximations, not rigorous truncated upper bounds.
The formal projection coefficient is
$$1/a_*+a_* /(2-a_*)^2$$, where $$a_*\in(0,1)$$ is the unique root of
$$a_*^3-2a_*^2+6a_*-4=0$$. The planar Poisson coefficient is

$$
\frac{e\,a_P(2)}{2(1+a_P(2))^{3/2}}
+\frac1{\sqrt{1+e\,a_P(2)}}.
$$

The one- and two-dimensional heat coefficients are respectively

$$
4\sqrt{a_H(1)/\pi}\,e^{-a_H(1)}
+\operatorname{erfc}(2\sqrt{a_H(1)}),\qquad
[1+(e-1)a_H(2)]e^{-a_H(2)},
$$

where $$\operatorname{erfc}(r)=\frac2{\sqrt\pi}\int_r^\infty e^{-s^2}\,ds$$.
The source proves parameter existence, uniqueness, and the equality of these
special formulas with the general formulas.

## Proof development

The linear branch constructs actual whole-space vector and complex Poisson
balayage, proves Sobolev regularity and zero-set cancellation, and derives the
full vector and Frobenius matrix estimates. Genuine linear extensions give
bounds for every complex $$L^1$$ input. Leray and gradient projections act on
vector fields; the Riesz and Hessian estimates use the full outputs.

The semigroup branch constructs positive whole-space Laplace balayage and
integrable tangent majorants, computes their exact masses, and transfers the
estimates to every positive time and every integrable input. The final bounds
have no analytical certificate assumptions. The interval and Euclidean-ball
proofs are adapted from the author's
[earlier formalization](https://github.com/CoolRmal/centered-maximal-constant/tree/72c022ba09032b522c878cca2f9b6c68217d77ea).

## Verification and layout

An earlier fifteen-row snapshot,
`e301f763ae0c819976384ea733f7327e80ce1c44`, including full complex-input Riesz,
[passed official full Palomar preflight](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37404883784)
with zero errors and warnings. Its solution was accepted by Comparator and
Lean, NanoDa, and con-ron. The cleaned current snapshot requires fresh ordinary
CI and official full verification. The repository is **not registered on
Palomar**. [Verification history](docs/VERIFICATION.md) distinguishes the
historical pass from the unsuccessful sixteen-row attempts.

- `Challenge.lean`: fifteen independent statements importing Mathlib alone.
- `Solution.lean`: the matching proved declarations.
- `PartialBalayage/`: the partial-balayage development and table adapters.
- `CenteredMaximal/`: the retained earlier source dependencies with author headers.
- `comparator.json`: the exact fifteen compared statements.
- `formalization.yaml`: provenance, scope, and review metadata.
- [docs/DECOMPOSITION.md](docs/DECOMPOSITION.md): definitions and proof map.
- [docs/PALOMAR.md](docs/PALOMAR.md): verification and registration procedure.

Lean and Mathlib are pinned. Build with `lake exe cache get`, then `lake build`.
Deliberate Challenge holes state the problems and do not enter Solution.
A source build alone does not establish Comparator or independent-kernel
acceptance. Registration requires successful checks and the human author's
consent to the exact subsequent review.
Submission uses [Palomar's intake](https://submit.palomar-registry.org/).

## Provenance and licence

Mathematics and human authorship: Yongxi Lin. Codex and collaborating agents
assist with formalization and verification; no AI system is listed as an author.
The template comes from
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406).
Code is Apache-2.0. No external human review has been obtained.
