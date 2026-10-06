# Scope and proof decomposition

The current source and Comparator include fifteen rows of Yongxi Lin's
[article table](https://coolrmal.github.io/articles/two-partial-balayage-principles/).
The [README](../README.md#complete-article-table-and-current-scope) lists all sixteen
article rows and marks the planar square bound $$c(M_\square)<3.616$$ as excluded.
Its large arithmetic certificates made complete verification difficult; the square
proof and numerical development have been removed from the current scope.
The separate repository
[centered-maximal-constant](https://github.com/CoolRmal/centered-maximal-constant)
formalizes the weaker square bound $$c(M_\square)\le3.879$$.

## Operator definitions

The weak-type constant is the infimum of the nonnegative extended-real constants
$$C$$ satisfying the level-set estimate for every integrable input:

$$
\lambda\,|\{x:\|Tf(x)\|>\lambda\}|\le C\int\|f(x)\|\,dx.
$$

The maximal statements cover every extended-real level. The linear statements use
canonical complex Fourier operators and their genuine $$L^1$$ extensions.
The vector norm is Euclidean/Hermitian and the matrix norm is Frobenius.
The Riesz operator is the full vector transform, the second-order transform is the
full matrix transform, and both projections act on vector fields.

The relevant multipliers, with harmless values at the zero frequency, are

$$
\widehat{Rf}(\xi)=\frac{i\xi}{|\xi|}\widehat f(\xi),\qquad
\widehat{Bf}(\xi)=\frac{(\xi_1-i\xi_2)^2}{|\xi|^2}\widehat f(\xi),
$$

$$
\widehat{\mathcal H_nf}(\xi)=-\frac{\xi\otimes\xi}{|\xi|^2}\widehat f(\xi),
\qquad \mathcal H_{0,n}f=\mathcal H_nf+\frac fn I,
$$

$$
\widehat{\mathbb Qf}(\xi)=\frac{\xi\otimes\xi}{|\xi|^2}\widehat f(\xi),
\qquad \mathbb P=I-\mathbb Q.
$$

The interval and Euclidean-ball operators average the absolute value of a real
integrable function over every centred interval or Euclidean ball. The semigroup
maximal operators are

$$
P_*f(x)=\sup_{t>0}(p_t*|f|)(x),\qquad
p_t(x)=\frac{\Gamma((n+1)/2)}{\pi^{(n+1)/2}}
       \frac{t}{(t^2+|x|^2)^{(n+1)/2}},
$$

$$
H_*f(x)=\sup_{t>0}(h_t*|f|)(x),\qquad
h_t(x)=(4\pi t)^{-n/2}e^{-|x|^2/(4t)}.
$$

Euclidean balls use `EuclideanSpace ℝ (Fin n)` and its Euclidean norm.
The retained one-dimensional cube formulation gives centred intervals.

## The fifteen included statements

| Article rows | Public Solution declaration | Scope |
| --- | --- | --- |
| 1 | `riesz_weakTypeConstant_le_two` | Full complex-input Riesz vector, $$n\ge1$$ |
| 2 | `beurling_weakTypeConstant_le_two` | Complex scalar inputs on the plane |
| 3 | `hessian_weakTypeConstant_two_le_exact` | Full planar Frobenius Hessian |
| 4 | `hessian_weakTypeConstant_le_formula` | Full Frobenius Hessian, $$n\ge2$$ |
| 5 | `tracelessHessian_weakTypeConstant_le` | Traceless Frobenius Hessian, $$n\ge1$$ |
| 6 | `projections_weakTypeConstants_le_exact` | Both projections, $$n\ge2$$ |
| 7 | `interval_weakTypeConstant_le_two` | Centred intervals |
| 8 | `ball_weakTypeConstant_two_le_exp` | Planar Euclidean balls |
| 10 | `ball_weakTypeConstant_le_rpow` | Euclidean balls, $$n\ge3$$ |
| 11 | `poisson_weakTypeConstant_one_le_exact` | Exact one-dimensional Poisson expression |
| 12 | `poisson_weakTypeConstant_two_le_exact` | Exact planar Poisson expression |
| 13 | `poisson_weakTypeConstant_le_formula` | Poisson formula, $$n\ge1$$ |
| 14 | `heat_weakTypeConstant_one_le_exact` | Exact one-dimensional heat expression |
| 15 | `heat_weakTypeConstant_two_le_exact` | Exact planar heat expression |
| 16 | `heat_weakTypeConstant_le_formula` | Heat formula, $$n\ge1$$ |

The dimension-one traceless operator is zero. The projection statement contains
both inequalities. The approximate decimals in the article are labels for exact
expressions; they are not substituted as rigorous truncated upper bounds.
The README gives the exact parameters and formulas. Their existence and uniqueness
are proved for every positive dimension, without an assumed root certificate.

## Linear proof map

1. Concrete Fourier multipliers specify the Riesz, Beurling, full and traceless
   Hessian, and projection operators with the intended output norms.
2. Whole-space vector balayage constructs the norm-capped decomposition and proves
   its weak PDE, active-volume bound, and global Sobolev regularity.
3. Physical Sobolev zero-set locality gives Hessian and projection cancellation.
   The complex Poisson branch constructs the Riesz decomposition, proves the
   frequency-norm identity and self-energy pairing, identifies every coordinate
   with a physical derivative, and obtains full-vector cancellation.
4. The norm-capped level-set estimates give the exact coefficients. Genuine linear
   extensions, unique among finite weak-bound extensions, transfer the operators
   to every complex $$L^1$$ input.

The principal source groups are `PartialBalayage/Linear/`,
`PartialBalayage/Constants/`, `TableDefinitions.lean`, and
`ComplexTableDefinitions.lean`. No input-dependent decomposition, locality, or
Fourier certificate is left as a hypothesis of the public table statements.

## Maximal proof map

1. The interval and Euclidean-ball bounds reuse the author's earlier development,
   retaining its source attribution and Apache-2.0 headers.
2. Positive whole-space Laplace balayage supplies cap complementarity and the
   active-volume estimate for the semigroup branch.
3. Harmonic tangent majorants genuinely dominate the original Poisson and heat
   kernels. Radial comparison and integration compute their exact masses.
4. Parameter existence and uniqueness, Gaussian and arctangent tails, and planar
   elementary identities produce the exact general and special coefficients.
5. Rational-time comparison, continuity, and monotone integrable truncations give
   every positive time and every integrable input.

These proofs are in `PartialBalayage/Maximal/` and the retained
`CenteredMaximal/` dependencies. The public conclusions have no analytical
certificate hypotheses.

## Verification boundary

The source statements are matched by `Challenge.lean`, `Solution.lean`, and the
fifteen targets in `comparator.json`. Deliberate Challenge holes do not enter the
solution. The permitted axioms are only `propext`, `Classical.choice`, and
`Quot.sound`; a declaration may use a subset.

The earlier corrected fifteen-row snapshot passed the official full check.
That historical result does not establish acceptance of the newly cleaned
snapshot. Fresh ordinary CI and the protected official full verification are
required before intake. [VERIFICATION.md](VERIFICATION.md) records the historical
scope and failed sixteen-row attempts; registration remains pending.
