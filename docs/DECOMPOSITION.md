# Scope and mathematical decomposition

The source for this project is the online article [Two partial balayage principles for
weak-type estimates](https://coolrmal.github.io/articles/two-partial-balayage-principles/),
as fetched on 5 October 2026. Its abstract contains sixteen rows. The local manuscript
contains a different table, so its additional applications do not replace or extend the
requested target. The target consists of the sixteen asserted upper bounds, including
the exact expressions represented by approximate decimals. Cited sharp comparisons,
asymptotic estimates, and optimality of the majorants are useful context but are not
additional final targets.

## Definitions required by the statements

Use Lebesgue measure on the Euclidean space of dimension $$n$$. For an operator $$T$$,
the weak-type constant is the infimum of all nonnegative extended-real constants $$C$$
for which

$$
\lambda\,|\{x:|Tf(x)|>\lambda\}|\le C\int |f(x)|\,dx
\qquad(\lambda>0).
$$

The final maximal inequalities quantify over all integrable scalar inputs. Their
definitions can use nonnegative extended-real integrals and outer measure, as in the
existing centered-maximal project. For the linear operators, Fourier multipliers give
canonical bounded operators on complex-valued $$L^2$$. The weak estimate must hold for
every input in $$L^1\cap L^2$$, and a density/convergence-in-measure construction must
identify the resulting extension to all $$L^1$$. If a challenge initially uses the
standard $$L^1\cap L^2$$ formulation of weak type for an $$L^2$$ operator, document and
prove this equivalence; an extra decomposition hypothesis on each input is not a
substitute for the article's unconditional operator estimate.

For vector outputs use the Euclidean/Hermitian norm. For matrix outputs use the
Frobenius norm, not an inherited matrix operator norm or a product sup norm. In Lean,
`EuclideanSpace ℂ (Fin n × Fin n)` is a convenient realization of the matrix output
space. Likewise, `EuclideanSpace ℝ (Fin n)` gives Euclidean balls, whereas
`Fin n → ℝ` has the sup norm and its metric balls are cubes.

The linear operators are specified by these multipliers, with any harmless value at
the zero frequency:

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

The Beurling operator acts on complex scalar inputs on the plane; the Riesz operator
is the full vector transform; the second-order operator is the full matrix transform.
Leray and gradient projections act on vector fields. Restricting to one Riesz
component, one matrix entry, or real-only Beurling inputs would weaken the target.

The maximal operators are

$$
M_cf(x)=\sup_{r>0}\frac1{2r}\int_{x-r}^{x+r}|f(y)|\,dy,
$$

$$
M_{B,n}f(x)=\sup_{r>0}\frac1{\omega_n r^n}\int_{B(x,r)}|f(y)|\,dy,
\qquad \omega_n=\frac{\pi^{n/2}}{\Gamma(n/2+1)},
$$

$$
M_\square f(x)=\sup_{r>0}\frac1{4r^2}\int_{x+[-r,r]^2}|f(y)|\,dy,
$$

$$
P_*f(x)=\sup_{t>0}(p_t*|f|)(x),\qquad
p_t(x)=\frac{\Gamma((n+1)/2)}{\pi^{(n+1)/2}}
       \frac{t}{(t^2+|x|^2)^{(n+1)/2}},
$$

$$
H_*f(x)=\sup_{t>0}(h_t*|f|)(x),\qquad
h_t(x)=(4\pi t)^{-n/2}\exp\left(-\frac{|x|^2}{4t}\right).
$$

## Exact sixteen-row target list

Write $$c(T)$$ for the weak-type constant just defined. Define

$$
\rho_n=\begin{cases}
(n/2)^{2/(n-2)},&n\ne2,\\
e,&n=2.
\end{cases}
$$

For the Poisson formula, let $$a_P(n)$$ be the unique solution in
$$\left(n/(3\rho_n),n/3\right)$$ of

$$
\frac{1-a/n}{(1+a)^{(n+3)/2}}
=\frac1{(1+\rho_n a)^{(n+1)/2}},
\qquad b_P(n)=\rho_n a_P(n),
$$

and define the exact bound

$$
B_P(n)=\frac{\Gamma((n+1)/2)}{\sqrt\pi\,\Gamma(n/2)}
\left[
\frac{2b_P(n)^{n/2}}{n(1+a_P(n))^{(n+1)/2}}
+\int_{b_P(n)}^\infty\frac{z^{n/2-1}}{(1+z)^{(n+1)/2}}\,dz
\right].
$$

For the heat formula, let $$a_H(n)$$ be the unique solution in
$$\left(n/(2\rho_n),n/2\right)$$ of

$$
e^{-(\rho_n-1)a}=1-\frac{2a}{n},
\qquad b_H(n)=\rho_n a_H(n),
$$

and define

$$
B_H(n)=\frac1{\Gamma(n/2)}
\left[
\frac{2b_H(n)^{n/2}e^{-a_H(n)}}n
+\int_{b_H(n)}^\infty z^{n/2-1}e^{-z}\,dz
\right].
$$

Both root definitions require proved existence and uniqueness for every positive
integer dimension. An unconstrained `Classical.choose` from an assumed root would
leave part of the unconditional target unproved. Define dimensions below one only
if the total Lean definitions need default values; the final statements require
$$n\ge1$$.

1. **Riesz vector transform**, every positive dimension:

   $$c(R)\le2.$$

2. **Beurling–Ahlfors transform**, complex scalar inputs on the plane:

   $$c(B)\le2.$$

3. **Full second-order Riesz transform**, dimension two, Frobenius norm:

   $$c(\mathcal H_2)\le\frac{3\sqrt6}{4}.$$

4. **Full second-order Riesz transform**, every $$n\ge2$$:

   $$
   c(\mathcal H_n)\le\frac1{a_n}+\frac{(n-1)a_n}{n-a_n^2},
   \qquad
   a_n=\sqrt{\frac{2n}{n+1+\sqrt{(n+1)^2+4(n-2)}}}.
   $$

5. **Traceless second-order Riesz transform**:

   $$c(\mathcal H_{0,n})\le2\sqrt{1-1/n}.$$

   Use $$n\ge2$$ for the nontrivial family; the formula also gives zero in dimension
   one, where the traceless transform is zero.

6. **Both Leray and gradient projections**, every $$n\ge2$$:

   $$
   c(\mathbb P),c(\mathbb Q)\le
   \frac1{a_*}+\frac{a_*}{(2-a_*)^2},
   $$

   where $$a_*$$ is the unique root in $$0<a_*<1$$ of

   $$a_*^3-2a_*^2+6a_*-4=0.$$

7. **Centered interval maximal operator**:

   $$c(M_c)\le2.$$

8. **Centered planar Euclidean-ball maximal operator**:

   $$c(M_{B,2})\le e.$$

9. **Centered planar axis-parallel-square maximal operator**:

   $$c(M_\square)<3.616.$$

   The body supplies the stronger bound $$c(M_\square)\le C_{6/5}<3.615749$$.
   The old bound $$3.879$$ cannot discharge this row.

10. **Centered Euclidean-ball maximal operator**, every $$n\ge3$$:

    $$c(M_{B,n})\le(n/2)^{n/(n-2)}.$$

11. **Poisson maximal operator**, dimension one:

    $$
    c(P_{*,1})\le1+\frac2\pi
    \left(\frac{\sqrt5}{3}-\arctan\frac2{\sqrt5}\right).
    $$

    The root values are exactly $$a_P(1)=1/5$$ and $$b_P(1)=4/5$$.

12. **Poisson maximal operator**, dimension two:

    $$c(P_{*,2})\le B_P(2).$$

    An equivalent elementary expression is

    $$
    B_P(2)=\frac{e\,a_P(2)}{2(1+a_P(2))^{3/2}}
           +\frac1{\sqrt{1+e\,a_P(2)}}.
    $$

13. **Poisson maximal operator**, every positive dimension:

    $$c(P_{*,n})\le B_P(n).$$

14. **Heat maximal operator**, dimension one:

    $$
    c(H_{*,1})\le4\sqrt{\frac{a_H(1)}\pi}e^{-a_H(1)}
                  +\operatorname{erfc}(2\sqrt{a_H(1)}),
    $$

    where $$e^{-3a_H(1)}=1-2a_H(1)$$ and

    $$\operatorname{erfc}(r)=\frac2{\sqrt\pi}\int_r^\infty e^{-s^2}\,ds.$$

    The expression must be proved equal to $$B_H(1)$$.

15. **Heat maximal operator**, dimension two:

    $$c(H_{*,2})\le[1+(e-1)a_H(2)]e^{-a_H(2)}.$$

    Here $$e^{-(e-1)a_H(2)}=1-a_H(2)$$. Prove that this expression equals
    $$B_H(2)$$.

16. **Heat maximal operator**, every positive dimension:

    $$c(H_{*,n})\le B_H(n).$$

## Rounding and formulation issues

The approximate decimals in the abstract are labels for exact upper bounds, not
rigorous rational bounds. In particular, the exact projection bound is
$$1.805359306638\ldots$$, the planar Poisson expression is numerically
$$1.0210358633897\ldots$$, and the two heat expressions are
$$1.037087059430\ldots$$ and $$1.094052157640\ldots$$. Each exceeds the corresponding
truncated decimal in the table. State the exact expressions above; any optional
decimal upper corollary must round upward and have a certified proof.

The online table does not request the cited sharp real-input planar matrix theorem,
the sharp interval constant, or a proof of the asymptotics. The projection row
contains two operators and therefore needs two final estimates. The article's
``second-order Riesz transform'' is matrix-valued and uses the Frobenius norm.

The article's maximal principle explicitly assumes a conservative symmetric Markov
convolution generator, its homogeneity, and its partial-balayage construction. A
statement quantifying over arbitrary operators while retaining only off-origin
kernel positivity would omit essential hypotheses. These assumptions are suitable
for proving the abstract principle; every concrete final table bound must discharge
them for its particular generator and kernel.

There is no detected contradiction in the asserted table bounds. The substantial
proof gaps from the perspective of the existing Lean API are recorded below; the
article's short variational, Sobolev zero-set, and Courrège arguments should not be
treated as already formalized facts.

## Proof dependency decomposition

### Linear branch

1. Construct the scalar and finite-dimensional Hilbert-valued partial balayage
   decomposition for $$0<\alpha\le2$$, including signed and complex inputs:

   $$
   f=\mu+(-\Delta)^{\alpha/2}u,\quad
   \|\mu\|_\infty\le\kappa,\quad
   \|\mu\|_1\le\|f\|_1,\quad
   \mu=\kappa u/|u|\text{ on }\{u\ne0\}.
   $$

   Prove the contact-set estimate, the required Sobolev/operator regularity, and the
   almost-everywhere derivative vanishing on the zero set. Orders one and two cover
   all the requested linear examples; proving every intermediate fractional order
   is an optional strengthening of the abstract principle.

2. Prove the elementary weak estimate from this decomposition and locality. It is
   the Chebyshev estimate

   $$
   \lambda|\{|Tf|>\lambda\}|\le
   \left(\frac\lambda\kappa+\frac{M^2\kappa}\lambda\right)\|f\|_1,
   $$

   followed by $$\kappa=\lambda/M$$, with a separate zero-operator case.

3. Build the actual Fourier-multiplier operators, prove their norm bounds and local
   compositions. Riesz uses order one; Beurling, matrices and projections use
   order two. Mathlib's Fourier transform uses the $$2\pi$$ convention, so
   fractional Laplacian and derivative identities need the matching factors.

4. Prove the pointwise trace orthogonality identity and the traceless energy bound.
   The sharpened full-matrix estimate is

   $$
   \frac1a+\frac{(n-1)a}{n-a^2}\qquad(0<a<\sqrt n).
   $$

   Optimize it by the quartic equation

   $$(n-2)a^4+n(n+1)a^2-n^2=0.$$

5. Prove the identity-component variant and apply it to both projections with
   $$c=M=1/2$$. The objective is

   $$\frac1a+\frac{a}{(2-a)^2}\qquad(0<a<2).$$

   Prove the minimizing cubic root's existence, uniqueness, and admissibility.

6. Extend from $$L^1\cap L^2$$ to $$L^1$$ and verify that all actual operator
   definitions in the final statements agree with those extensions.

### Maximal branch

1. Preserve the existing interval and ball results and their direct definitions.
   These already discharge rows 7, 8, and 10 after transporting definitions.

2. Extract or generalize a kernel transfer theorem for the Laplacian and for the
   two-coordinate stable generator of order $$6/5$$. A general Courrège theorem is
   absent from Mathlib; the concrete generators can instead use direct positive
   measure-minus-atom representations and the existing weak pairing/obstacle
   machinery. The transfer still needs to handle every dilation outside one common
   null set and approximation from bounded compactly supported inputs to all
   integrable inputs.

3. For the square bound, formalize the supplied fractional profile and cubic-spline
   correction, domination of the unit-diamond indicator, off-origin generator
   positivity, and its exact mass. Lift every rational/fifth-root certificate into
   kernel-checked Lean arithmetic. Generalize the old transfer assembly from its
   hard-coded order-one kernel to order $$6/5$$. The diamond-to-square linear change
   of variables is already proved in the earlier project.

4. For Poisson and heat, prove the root existence/uniqueness statements, construct
   the piecewise radial harmonic tangent majorants, prove domination and the
   nonnegative distributional flux jump, and compute their masses by polar
   integration. The outer tails are not compactly supported, so ball-kernel results
   cannot be reused verbatim where they require compact support.

5. Identify all positive-time Poisson and heat kernels with dilations of the base
   kernels $$p_1$$ and $$h_{1/4}$$. Prove the one- and two-dimensional evaluations
   as corollaries of the general bounds.

## Existing results and missing API

The existing `centered-maximal-constant` development already contains:

- `CenteredMaximal.isWeakTypeBound_two_pow`, hence the interval bound at dimension
  one;
- exact planar and higher-dimensional Green kernel masses and all-scale weak bounds,
  culminating in the two ball theorems in its `Solution.lean`;
- `CenteredMaximal.exists_obstacle_solution` for the two-coordinate stable jump
  generator at every order strictly between zero and two, for bounded nonnegative
  compactly supported scalar inputs;
- jump forms, a real Hilbert energy space, positive-cone minimization, density
  extraction, complementarity, mass conservation, scaling, convolution commutation,
  rational-scale reduction, and approximation to all integrable inputs;
- a direct positive-measure-minus-point-mass representation for the old order-one
  Cauchy kernel, and the determinant-two diamond-to-square change of variables;
- bounded-domain scalar Laplacian penalty solutions, weak limits, capped complement
  densities, a local distributional equation, and local contact-mass control.

The old square theorem only proves the earlier value $$3.879$$. Its `Cauchy` modules
contain many facts specifically tied to the old order-one potential and old explicit
kernel; those facts do not certify the new fractional spline kernel.

Mathlib provides `MeasureTheory.Lp.fourierTransformₗᵢ`,
`MeasureTheory.Lp.norm_fourier_eq`, tempered distributions, Fourier differentiation,
and `TemperedDistribution.MemSobolev` with Fourier and derivative characterizations.
These are usable foundations, but searches found no Riesz/Beurling/Leray operators,
Euclidean heat/Poisson semigroup maximal theorem, Hilbert-valued balayage theorem,
Courrège theorem, or Sobolev zero-set derivative theorem matching the required
application. Its complex disk Poisson kernel is a different object from the
Euclidean Poisson semigroup kernel here. No existing `erf`/`erfc` definition was
found; the integral definition is sufficient for the exact dimension-one heat row.

The scalar local ball framework is not a proof of the signed/vector global
decomposition. Its equation is only tested inside the ball, its sources are
nonnegative real-valued functions, and its principal cap argument uses the order
structure of scalar $$L^2$$. Reuse its general Hilbert-space variational and
compactness lemmas after supplying the missing vector, whole-space, and fractional
steps; do not add the desired decomposition as a final theorem hypothesis.

## Implementing the signed and vector obstacle

The strongest reusable components are the genuinely abstract real-Hilbert lemmas in
`Ball/ObstacleExistence.lean`, `Ball/MonotoneSurjectivity.lean`, and
`Analysis/WeakCompact.lean`. In particular,
`exists_eq_of_stronglyMonotone_lipschitz` applies to arbitrary nonlinear maps on a
complete real Hilbert space. It can solve a radial vector penalty after proving its
Lipschitz and monotonicity properties. It does not require scalar order. The concrete
negative-part implementation in `Ball/L2Penalty.lean` does require scalar order and
must be replaced, rather than applied to vector fields component by component. A
componentwise cap would give the wrong Euclidean cap and dimension dependence.

A bounded-domain dual construction can avoid the radial-penalty limit. Let
$$D$$ be a ball, take the finite Hilbert product of the existing scalar
$$H^1_0(D)$$ spaces, and let $$J$$ be its value embedding into $$L^2(D;E)$$.
Treat complex $$E$$ as a real Hilbert space. Let $$A$$ be the coercive positive
Dirichlet operator represented in this Hilbert space. The existing coercive solver
gives $$A^{-1}$$. Set

$$
G=J A^{-1}J^*,\qquad
K_\kappa=\{\mu\in L^2(D;E):|\mu(x)|\le\kappa\text{ almost everywhere}\}.
$$

The cap set is nonempty, convex, closed and bounded because $$D$$ has finite
measure, hence weakly compact by `Analysis/WeakCompact.lean`. Minimize the continuous
convex quadratic

$$
Q(\mu)=\frac12\langle f-\mu,G(f-\mu)\rangle
\qquad(\mu\in K_\kappa).
$$

The weak direct method yields a minimizer without a positive-cone assumption. Put
$$u=A^{-1}J^*(f-\mu)$$. The first-order variational inequality is

$$\langle Ju,\nu-\mu\rangle\le0\qquad(\nu\in K_\kappa).$$

Take the measurable admissible candidate $$\nu=\kappa Ju/|Ju|$$ on
$$\{Ju\ne0\}$$ and zero elsewhere. The pointwise upper bound
$$\langle Ju,\mu\rangle\le\kappa|Ju|$$ and equality of the integrals force

$$\mu=\kappa Ju/|Ju|\qquad\text{almost everywhere on }\{Ju\ne0\}.$$

This gives the signed/vector local equation and exact norm saturation. It uses only
finite-domain $$L^2$$ compactness. `Linear/DirichletDual.lean` now proves the abstract
positive Green construction and this dual state equation for a coercive Dirichlet
operator and value embedding. `Linear/CapComplementarity.lean` proves the actual
measurable support competitor, integral equality, vector alignment, and saturation.
`Linear/VectorDirichlet.lean` now instantiates the finite-product Sobolev value map
and the actual Poincaré-coercive Dirichlet operator. It supplies the concrete
coordinatewise weak Laplace equations, cap, alignment, and active-set saturation.

The local construction alone is insufficient for the whole-space theorem. One
route is to exhaust the space by balls and prove uniform energy, $$L^1$$ and $$L^2$$
bounds before taking weak limits. The zero extension of an individual local
Dirichlet solution has a boundary flux, so its local equation must not be asserted
as a whole-space equation. The boundary disappears only after passing to a limit
against tests contained in each sufficiently large ball.

For the local order-two vector problem, regularity and Sobolev chain/zero-set lemmas
give a concrete path to the required mass estimate. Test the equation by the
regularized norm gradient, let the regularization vanish, and obtain

$$
\kappa|\{u\ne0\}|\le\int_{\{u\ne0\}}|f|.
$$

On the zero set, second weak derivatives vanish and therefore $$\mu=f$$.
Combining the two regions gives $$\|\mu\|_1\le\|f\|_1$$. This is stronger than
the contact-set bound alone and provides the uniform bound
$$\|\mu\|_2^2\le\kappa\|f\|_1$$ for an exhaustion. The vector norm-gradient
chain rule is proved in `Linear/VectorSobolevComposition.lean`; second-derivative
regularity and its localization remain substantive missing API.
`Linear/SobolevZeroSet.lean` proves first-gradient vanishing on zero sets, and equality
of gradients on equality sets, for the actual copied Sobolev graph space on every
open domain. `Linear/SecondSobolevZeroSet.lean` iterates this vanishing for actual
second-gradient graphs. It does not assert that all Dirichlet gradients belong to
the global zero-boundary Sobolev space. `Linear/VectorSobolevComposition.lean` proves
the regularized vector norm test's admissibility for every positive regularization.

An alternative whole-space implementation more closely follows
`Obstacle/Functional.lean`: build the vector Hilbert energy space and minimize

$$
\frac12\mathcal E(u,u)+\kappa\|u\|_1-\operatorname{Re}\int\langle f,u\rangle.
$$

On finite balls, the integral of the norm is continuous and convex as a function of
the $$L^2$$ value coordinate, so the existing convex weak-lower-semicontinuity lemma
applies. Taking the increasing supremum over balls gives weak lower semicontinuity
of the full $$L^1$$ norm for signed/vector functions. This replaces the old scalar
argument that represents the positive $$L^1$$ norm by linear integrals.
The old coercivity proof then needs a norm version of its local Gagliardo/Nash
estimate and a dimension-general energy space. This direct method avoids proving
Rellich compactness merely to identify a nonlinear exhaustion limit.

For the Riesz row the order-one generator must be the isotropic
$$(-\Delta)^{1/2}$$. The existing two-coordinate generator
$$|D_1|+|D_2|$$ is different and does not make the actual Riesz composition local.
Use the isotropic fractional energy or the Fourier-defined Sobolev space, prove the
norm contraction/Kato inequality using its positive mass-preserving semigroup, and
extract the same capped density. Positivity and mass preservation of that semigroup,
its operator-domain convergence, and the cutoff decay estimate are genuine
dependencies. The order-one scalar/complex construction cannot be replaced by the
existing order-two ball obstacle.

## Further verified support

The unique heat and Poisson parameters now satisfy the article's exact intervals in
every positive dimension. `Maximal/RadialTangentMass.lean` proves the weighted mass
identities for power and logarithmic harmonic tangents. `Maximal/HeatMajorant.lean`
and `Maximal/PoissonMajorant.lean` prove actual domination at every positive squared
radius, joining at the outer radius, and a strictly positive outward derivative
jump for the respective profiles. The origin is excluded
from these real profile statements; its artificial totalized value is irrelevant
to a future almost-everywhere kernel statement in positive dimension. Distributional
kernel inequalities and the resulting maximal estimates are still pending.

`Linear/ProjectionSymbol.lean` proves actual gradient and Leray symbols are
orthogonal projections and that their shifts by half the identity have norm at
most one half. `Linear/IdentityComponent.lean` and `Linear/OrthogonalComponent.lean`
prove the exact level-set coefficients from explicit decomposition hypotheses.
`Linear/OperatorMultiplier.lean` constructs actual bounded operator-valued Fourier
multipliers, and `Linear/ProjectionMultiplier.lean` instantiates the gradient and
Leray projections, their contractions, and their exact half-identity decompositions.
`Linear/FourierPostcomposition.lean` proves constant output maps commute with Fourier
and inverse Fourier on L² via Schwartz density. `Linear/HessianTrace.lean` proves the
actual Hessian trace, traceless splitting, and pointwise Pythagorean norm identity.

`Linear/VectorDirichletMass.lean` proves the regularized vector norm direction's
actual Frechet derivative and positive Jacobian quadratic form. Its dominated-limit
and genuine Sobolev weak-equation testing theorems give the active-volume estimate
once simultaneous admissible vector composition graphs are constructed. That
construction has now been discharged by `Linear/VectorSobolevComposition.lean`,
which proves the multivariate Sobolev chain rule and the concrete finite-domain
active-volume estimate. `Linear/VectorActiveMass.lean` now proves the sharper
restricted active-mass estimate and the total density-mass consequence once actual
inactive-set locality is supplied. `Linear/VectorBalayageFinite.lean` combines the
actual obstacle construction and testing into finite-domain existence, including
the active-volume bound and the active density's L² energy bound. It does not
assert a total density-mass estimate without the required locality argument.

`Linear/LocalSecondSobolev.lean` proves genuine global Fourier elliptic regularity:
an actual L² function with an L² weak Laplacian has represented L² second derivatives.
`Linear/LocalCutoffEquation.lean` and `Linear/LocalCutoffLaplacian.lean` prove the true
first- and second-order cutoff product identities from the actual H01 weak equation.
`Linear/LocalCutoffRegularity.lean` constructs the actual complex L² zero extension
of each interior cutoff and proves it has represented L² second derivatives using
Fourier H² regularity. The localized graph-closure and zero-set locality bridge
remains to be constructed.

`Linear/MollifierL2.lean` proves normalized nonnegative convolution is an actual
contraction on L². `Linear/MollifierL2Convergence.lean` proves strong convergence
of shrinking normalized bump convolutions for every L² class.
`Linear/SobolevSpatialCutoff.lean` constructs actual interior-cutoff H01 graphs,
including their represented gradients and support.

`Linear/L1NormFunctional.lean` proves continuous linear inclusion from actual
finite-measure vector L² into L¹, convexity of its norm, and weak lower
semicontinuity. `Linear/WholeSpaceL1Norm.lean` proves the full vector norm integral
is weakly lower semicontinuous on sigma-finite spaces by an exact exhaustion;
its mass sublevel sets are weakly closed, including infinite integral values.
`Linear/FourierL1L2.lean` proves the integral and unitary L² Fourier transforms
agree for integrable Hilbert-valued inputs. `Linear/FourierEnergySplit.lean`
proves the actual isotropic low/high-frequency estimate. `Linear/IsotropicEnergySpace.lean`
constructs the complete Hilbert energy graph and identifies its full Fourier energy.
`Linear/FourierCoercivity.lean` proves a positive small-frequency radius exists
in every positive dimension and the resulting quantitative energy and mass bounds.
`Linear/WholeSpaceMassCompactness.lean` proves weak compactness of the actual Hilbert L²
densities satisfying a pointwise norm cap and a finite full-vector mass bound, even
on an infinite measure space. It supplies density compactness for a future exhaustion;
the obstacle-state limit and its identification remain necessary.
`Linear/HessianCapEstimate.lean` discharges the energy and orthogonal
splitting conditions using the actual full and traceless Hessians. It supplies the
article's exact optimized Hessian coefficient from capped-density data; the
unconditional construction of that density is still required.

`Maximal/RadialFluxComparison.lean` proves the finite-annulus integration-by-parts
identity, including the joined-profile flux jump. `Maximal/RadialKernelComparison.lean`
proves the actual heat and Poisson flux monotonicity and jump signs. These are
prerequisites for the distributional kernel comparison. `Maximal/RadialKernelPairing.lean`
and `Maximal/SemigroupKernelPairing.lean` now prove actual ambient integrability and
nonnegative Laplacian pairings for nonnegative C² compact tests vanishing at the center,
for both exact-root majorants in every positive dimension. The supporting radial
integrability and sphere-geometry modules supply the center and support terms.
`Maximal/AffineRadialScaling.lean` and `Maximal/ScaledSemigroupMajorants.lean` prove
the actual normalized time-kernel identities, almost-everywhere domination, compact
integrability, and zero-contact pairings after translation and dilation. Transfer
to the actual Sobolev obstacle and the final maximal inequalities remain necessary.
`Maximal/PoissonKernel.lean` proves integrability and mass one of the genuine Poisson
kernel by Laplace-Gaussian integration, without a normalization assumption.
`Maximal/PoissonKato.lean` specializes norm-defect and Kato averaging to this actual
probability kernel. `Maximal/PlanarBoundFormula.lean` proves the exact
elementary planar heat and Poisson formulas, including their improper tails.
`Maximal/SquaredRadialMass.lean` and `Maximal/SemigroupMajorantMass.lean` prove
genuine ambient integrability and exact full masses of both normalized majorants,
in every positive dimension and at every positive time. The center-source modules
retain the finite center-value term for arbitrary nonnegative compact C² tests.
`Maximal/BoundedSourceTransfer.lean` proves this comparison for globally bounded
C² functions with bounded derivatives by genuine cutoff estimates and dominated
convergence. `Maximal/L2MollifiedSource.lean` constructs actual bounded positive
smooth mollifications of nonnegative L² states, derives their true Laplace equation
from the distributional equation, and applies the source comparison. Returning to
the original L² state and constructing the actual whole-space obstacle remain
necessary for the final maximal bounds.

These hypotheses must be discharged by concrete balayage before any additional
table row is added to the unconditional Challenge/Solution pair.

## Verification boundary

Each final challenge statement must name the concrete operators and exact
constants above and carry no unproved analytical certificate as a hypothesis.
Comparator success establishes equality between the challenge and solution
statements and verifies their permitted axioms; it does not establish that an
incorrectly weakened challenge is faithful to the source. Public metadata and
coverage should distinguish completed table rows from remaining proof work until
all sixteen rows are kernel checked.
