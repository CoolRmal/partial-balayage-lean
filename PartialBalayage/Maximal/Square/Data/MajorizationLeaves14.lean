/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices14

/-!
# Ordinary kernel checks of actual majorization leaves

Each literal array is checked against the actual signed spline pullback using the
proved sparse normalization. All Bernstein signs and all geometric vertex inequalities
are evaluated by the ordinary Lean kernel. No external data checker is a proof premise.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

/-- The actual closed rational triangle of majorization leaf 555. -/
def majorizationTriangle555 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 555. -/
def majorizationArray555 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2216217554984068200684724667244815151511997562029 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-89181461814387959308316221899764305022214026023 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1977789304844569 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-515910934664873 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-79537069064775509764618315503890548655982719783 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-63151206619213 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (25924080278813 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (57103879626981 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-617689886102329 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (2946994459979 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (-69313040611 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-108898542035327 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-128134899518731 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-3485279663117 /
    9375000000000000 : ℚ) else
  if p = (3, 2) then (-40912275488467 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (39886049236103 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf555_polynomial_eq :
    lowerPullbackPolynomial 12 6 majorizationTriangle555 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray555 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 6 majorizationTriangle555
    cellMatrix_12_6 cellMatrix_12_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf555_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray555 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf555_kernel {p : ℝ × ℝ} (hp : majorizationTriangle555.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 6 majorizationTriangle555
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray555
    majorizationLeaf555_polynomial_eq majorizationLeaf555_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 556. -/
def majorizationTriangle556 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 556. -/
def majorizationArray556 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (42377231982013609287405255663453440238569472283 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (3852360580053862723712275666133908106466283019 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-3430471712459959 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (18791938575957 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (3197384093500997343465398727432965648986131979 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (32105132682249 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-289365994916121 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (113058751754701 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-2684075005672501 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (189820631135097 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-31733400392737 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3376376993939 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (98899019303039 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (-14197675215559 /
    37500000000000000 : ℚ) else
  if p = (3, 2) then (-12953274327913 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (39886049236103 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf556_polynomial_eq :
    lowerPullbackPolynomial 12 6 majorizationTriangle556 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray556 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 6 majorizationTriangle556
    cellMatrix_12_6 cellMatrix_12_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf556_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray556 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf556_kernel {p : ℝ × ℝ} (hp : majorizationTriangle556.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 6 majorizationTriangle556
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray556
    majorizationLeaf556_polynomial_eq majorizationLeaf556_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 557. -/
def majorizationTriangle557 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 557. -/
def majorizationArray557 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (119710155355887858844578784783461704747389960693 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-11643958290003138113799503412758315551774698017 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-4471489544354011 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-592674041708023 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-8881482067576426898880695004462951537578043937 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (184583591503499 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (430552441669073 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (108413754981469 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-903892658217799 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (37342172313847 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-21890609272043 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-6979197880003 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-98899019303039 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (-14197675215559 /
    37500000000000000 : ℚ) else
  if p = (3, 2) then (12953274327913 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-385434458081849 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf557_polynomial_eq :
    lowerPullbackPolynomial 12 7 majorizationTriangle557 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray557 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 7 majorizationTriangle557
    cellMatrix_12_7 cellMatrix_12_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf557_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray557 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf557_kernel {p : ℝ × ℝ} (hp : majorizationTriangle557.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 7 majorizationTriangle557
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray557
    majorizationLeaf557_polynomial_eq majorizationLeaf557_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 558. -/
def majorizationTriangle558 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 558. -/
def majorizationArray558 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (245271611499124374553648726023755438445917827 /
    495176015714152109959649689600000000000000000 : ℚ) else
  if p = (0, 1) then (6017799878394061219219578925754254498042027811 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-1343511583954623 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (60006303940391 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (1396518929578224360096409534185093840089582177 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (1, 1) then (725596252059969 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-404125124461599 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (19126521590913 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-1251703050659287 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (659659483642429 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-87621090422919 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (203186025860929 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (2613946277980949 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-152385989865279 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (307714812114371 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-385434458081849 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf558_polynomial_eq :
    lowerPullbackPolynomial 12 7 majorizationTriangle558 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray558 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 7 majorizationTriangle558
    cellMatrix_12_7 cellMatrix_12_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf558_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray558 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf558_kernel {p : ℝ × ℝ} (hp : majorizationTriangle558.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 7 majorizationTriangle558
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray558
    majorizationLeaf558_polynomial_eq majorizationLeaf558_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 559. -/
def majorizationTriangle559 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 559. -/
def majorizationArray559 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (100009659213464195423146510549170075685016176033 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-6384092395576947592697047269700530382346985251 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-19529723967119 /
    1875000000000000 : ℚ) else
  if p = (0, 3) then (-4654339940545309 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-3704653493999703563698051032821259310892654371 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (158775724974899 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (486310608288209 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (613343610618239 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-71322679624807 /
    37500000000000000 : ℚ) else
  if p = (2, 1) then (-1582043078489 /
    1562500000000000 : ℚ) else
  if p = (2, 2) then (-4074707500007 /
    6250000000000000 : ℚ) else
  if p = (2, 3) then (-285812949267083 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-2613946277980949 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-152385989865279 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-307714812114371 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (268082824191859 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf559_polynomial_eq :
    lowerPullbackPolynomial 12 8 majorizationTriangle559 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray559 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 8 majorizationTriangle559
    cellMatrix_12_8 cellMatrix_12_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf559_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray559 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf559_kernel {p : ℝ × ℝ} (hp : majorizationTriangle559.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 8 majorizationTriangle559
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray559
    majorizationLeaf559_polynomial_eq majorizationLeaf559_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 560. -/
def majorizationTriangle560 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 560. -/
def majorizationArray560 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6957984065451058168178852488952911160590841483 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (34739283634300488523266083894320634389369987781 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-13268284605791 /
    1500000000000000 : ℚ) else
  if p = (0, 3) then (1276779090452531 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (17671364337836236258582292060687696643957727941 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (1330205216850963 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-765344528590179 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (375521310906253 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1583201528012369 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (410136270336081 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (138746197542431 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-715597847199457 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (921300676525567 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (1072074999710293 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-612315927140167 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (268082824191859 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf560_polynomial_eq :
    lowerPullbackPolynomial 12 8 majorizationTriangle560 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray560 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 8 majorizationTriangle560
    cellMatrix_12_8 cellMatrix_12_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf560_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray560 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf560_kernel {p : ℝ × ℝ} (hp : majorizationTriangle560.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 8 majorizationTriangle560
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray560
    majorizationLeaf560_polynomial_eq majorizationLeaf560_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 561. -/
def majorizationTriangle561 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 561. -/
def majorizationArray561 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1246595111587144648717327609398719249871959183309 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-122462708530252598310112185391681617337147746383 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-10903851610023389 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-944708801724029 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-37324206924293571794509103658031752996054657103 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (5373030514756543 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (562530409686227 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (2520855006784649 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-142756163298911 /
    24000000000000000 : ℚ) else
  if p = (2, 1) then (-378469508076491 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-1559455386335639 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-4372979090293611 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-921300676525567 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (1072074999710293 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (612315927140167 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (9459236339051 /
    1440000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf561_polynomial_eq :
    lowerPullbackPolynomial 12 9 majorizationTriangle561 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray561 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 9 majorizationTriangle561
    cellMatrix_12_9 cellMatrix_12_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf561_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray561 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf561_kernel {p : ℝ × ℝ} (hp : majorizationTriangle561.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 9 majorizationTriangle561
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray561
    majorizationLeaf561_polynomial_eq majorizationLeaf561_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 562. -/
def majorizationTriangle562 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 562. -/
def majorizationArray562 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4920766328234796786591356384888291655064348291 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (37429022528714637330777365246220432443919332767 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-141185373795667 /
    24000000000000000 : ℚ) else
  if p = (0, 3) then (-71107179896989 /
    72000000000000000 : ℚ) else
  if p = (1, 0) then (30024772560950875383210453694561096470917898461 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (3912234464037971 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (278865026844313 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1809554084024671 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-9256038395878459 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (1560179597569521 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-1017399451982221 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1294891847067083 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-17787211737629431 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (3314003197273009 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-13660993205234251 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (9459236339051 /
    1440000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf562_polynomial_eq :
    lowerPullbackPolynomial 12 9 majorizationTriangle562 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray562 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 9 majorizationTriangle562
    cellMatrix_12_9 cellMatrix_12_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf562_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray562 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf562_kernel {p : ℝ × ℝ} (hp : majorizationTriangle562.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 9 majorizationTriangle562
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray562
    majorizationLeaf562_polynomial_eq majorizationLeaf562_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 563. -/
def majorizationTriangle563 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 563. -/
def majorizationArray563 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (805211633299913669480217587913371658559037912183 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-164557464611880694364319546047035560343097139421 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-388124616510793 /
    12000000000000000 : ℚ) else
  if p = (0, 3) then (50269216164804583 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (27493746054216984413636284174515675677329366819 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (11801304822771029 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (770846354117719 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (-11210739032337053 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-2704325013350789 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (-9065097791967283 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-1834799082152059 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (14444133389142023 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (17787211737629431 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (3314003197273009 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (13660993205234251 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-40489477054581173 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf563_polynomial_eq :
    lowerPullbackPolynomial 12 10 majorizationTriangle563 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray563 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 10 majorizationTriangle563
    cellMatrix_12_10 cellMatrix_12_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf563_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray563 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf563_kernel {p : ℝ × ℝ} (hp : majorizationTriangle563.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 10 majorizationTriangle563
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray563
    majorizationLeaf563_polynomial_eq majorizationLeaf563_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 564. -/
def majorizationTriangle564 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 564. -/
def majorizationArray564 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (11744823391991089656559308236499444431380934179 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (22529863889073090624894117190384375623502035043 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (1782692882853139 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-5930392469238929 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-1037222936605161350797194746257087880878851997 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (2690797257730491 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-3564909796864153 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (2469561540190873 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-6436765676996479 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (6176632832493097 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2443921653858613 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (2919429054484077 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-9167095067754991 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-12362317237442933 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (4487864060261873 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (-40489477054581173 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf564_polynomial_eq :
    lowerPullbackPolynomial 12 10 majorizationTriangle564 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray564 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 10 majorizationTriangle564
    cellMatrix_12_10 cellMatrix_12_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf564_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray564 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf564_kernel {p : ℝ × ℝ} (hp : majorizationTriangle564.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 10 majorizationTriangle564
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray564
    majorizationLeaf564_polynomial_eq majorizationLeaf564_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 565. -/
def majorizationTriangle565 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 565. -/
def majorizationArray565 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (72843796615519415448189297861203858720998864519 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-35310322142973398036903925216403762176248019043 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (30862985339264933 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (13434810306225953 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (32330529088714843440468359979654598846595434397 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-1617231351434447 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-8127353615866177 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (58042885865345713 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-53248347911250889 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (4946737209468521 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (57542274288493643 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-40804038946105021 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (9167095067754991 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-12362317237442933 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-4487864060261873 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (10465243449973027 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf565_polynomial_eq :
    lowerPullbackPolynomial 12 11 majorizationTriangle565 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray565 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 11 majorizationTriangle565
    cellMatrix_12_11 cellMatrix_12_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf565_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray565 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf565_kernel {p : ℝ × ℝ} (hp : majorizationTriangle565.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 11 majorizationTriangle565
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray565
    majorizationLeaf565_polynomial_eq majorizationLeaf565_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 566. -/
def majorizationTriangle566 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 566. -/
def majorizationArray566 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (3509615909271575576846320556886142262454559469 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (33789265399506133643858980561603638254726578649 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (9218466406095163 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-695898291560869 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-15499944487839475818218606152271978151682845197 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-149370870103451 /
    6250000000000000 : ℚ) else
  if p = (1, 2) then (11336438233980351 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1862668503855563 /
    37500000000000000 : ℚ) else
  if p = (2, 0) then (-7195923079745939 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (-665474003856311 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (2479084829584589 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (-5761089151880057 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (446995836444133 /
    6250000000000000 : ℚ) else
  if p = (3, 1) then (-307171286887283 /
    12500000000000000 : ℚ) else
  if p = (3, 2) then (-2988689694855577 /
    20000000000000000 : ℚ) else
  if p = (3, 3) then (10465243449973027 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf566_polynomial_eq :
    lowerPullbackPolynomial 12 11 majorizationTriangle566 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray566 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 11 majorizationTriangle566
    cellMatrix_12_11 cellMatrix_12_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf566_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray566 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf566_kernel {p : ℝ × ℝ} (hp : majorizationTriangle566.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 11 majorizationTriangle566
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray566
    majorizationLeaf566_polynomial_eq majorizationLeaf566_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
