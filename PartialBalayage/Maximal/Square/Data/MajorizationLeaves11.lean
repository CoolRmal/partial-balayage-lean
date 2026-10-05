/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices11

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

/-- The actual closed rational triangle of majorization leaf 495. -/
def majorizationTriangle495 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 495. -/
def majorizationArray495 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2652673968898556101893502712428713641271113708467 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 2) then (-206996810821321 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (7077454332635797 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-210717049897930520834802050834097895952129396689 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 2) then (32603733437339 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (-62596871971291 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (-71415353191237 /
    15000000000000000 : ℚ) else
  if p = (2, 2) then (-2999235003511 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (1158978516263 /
    4800000000000000 : ℚ) else
  if p = (3, 0) then (18175162804547 /
    90000000000000000 : ℚ) else
  if p = (3, 2) then (275630250269 /
    30000000000000000 : ℚ) else
  if p = (3, 3) then (13134130011673 /
    1800000000000000000 : ℚ) else
  if p = (0, 1) then (-80550980241310418854043201205787404415445129883 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf495_polynomial_eq :
    lowerPullbackPolynomial 11 0 majorizationTriangle495 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray495 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 0 majorizationTriangle495
    cellMatrix_11_0 cellMatrix_11_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf495_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray495 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf495_kernel {p : ℝ × ℝ} (hp : majorizationTriangle495.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 0 majorizationTriangle495
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray495
    majorizationLeaf495_polynomial_eq majorizationLeaf495_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 496. -/
def majorizationTriangle496 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 496. -/
def majorizationArray496 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (8393218352652827913124911582843644450951394751 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (100297189006645980149512367736102046239410243077 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (187389100326329 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (-2354173083769 /
    900000000000000 : ℚ) else
  if p = (1, 0) then (29866512909760517145845862798849136726247610199 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (99611313225309 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (109212923510331 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-106012386748657 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-669618703104793 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (17726786431393 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (2721853088093 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (-39501611136137 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-393175201118753 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (8053113340811 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-18646735017053 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (13134130011673 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf496_polynomial_eq :
    lowerPullbackPolynomial 11 0 majorizationTriangle496 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray496 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 0 majorizationTriangle496
    cellMatrix_11_0 cellMatrix_11_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf496_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray496 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf496_kernel {p : ℝ × ℝ} (hp : majorizationTriangle496.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 0 majorizationTriangle496
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray496
    majorizationLeaf496_polynomial_eq majorizationLeaf496_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 497. -/
def majorizationTriangle497 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 497. -/
def majorizationArray497 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (103730917753433493410113594580813659882463367559 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 1) then (-100958386572518818539485063444470996696240113157 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (1255168453164887 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-36253824329931 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (-85043820487399203228870261563813721924395484677 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (73039251584839 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-57375682164517 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-259690596463 /
    2000000000000000 : ℚ) else
  if p = (2, 0) then (-40955333513839 /
    8000000000000000 : ℚ) else
  if p = (2, 1) then (-19013297149601 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (4980582878487 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (153742302693 /
    1250000000000000 : ℚ) else
  if p = (3, 0) then (393175201118753 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (8053113340811 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (18646735017053 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-29371796455957 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf497_polynomial_eq :
    lowerPullbackPolynomial 11 1 majorizationTriangle497 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray497 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 1 majorizationTriangle497
    cellMatrix_11_1 cellMatrix_11_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf497_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray497 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf497_kernel {p : ℝ × ℝ} (hp : majorizationTriangle497.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 1 majorizationTriangle497
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray497
    majorizationLeaf497_polynomial_eq majorizationLeaf497_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 498. -/
def majorizationTriangle498 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 498. -/
def majorizationArray498 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (20043113084609202564764182175987453391304266133 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (1685429199558109716494082234548379154300633837 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (449041751395171 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (251005616081803 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (1550364016510284693023899495295063448461345517 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (-256059025312197 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (236855804742153 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-6143319240497 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-554973277088531 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-1873069018173 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (29230565334257 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (4773028025077 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-21673901843467 /
    90000000000000000 : ℚ) else
  if p = (3, 1) then (-6665644827833 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (34734327175409 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-29371796455957 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf498_polynomial_eq :
    lowerPullbackPolynomial 11 1 majorizationTriangle498 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray498 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 1 majorizationTriangle498
    cellMatrix_11_1 cellMatrix_11_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf498_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray498 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf498_kernel {p : ℝ × ℝ} (hp : majorizationTriangle498.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 1 majorizationTriangle498
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray498
    majorizationLeaf498_polynomial_eq majorizationLeaf498_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 499. -/
def majorizationTriangle499 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 499. -/
def majorizationArray499 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (51431318036492830470180308653011733303735719359 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 1) then (-5016650795656528515504464738755508902239701191 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (1037645507185301 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-314243941842059 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-4354817800634673948330587161232193830838372551 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-2291741941279 /
    1600000000000000 : ℚ) else
  if p = (1, 2) then (-72957117952297 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (2189995647667 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-213889628154133 /
    40000000000000000 : ℚ) else
  if p = (2, 1) then (5707129665901 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (3947968787403 /
    8000000000000000 : ℚ) else
  if p = (2, 3) then (-12042578127399 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (21673901843467 /
    90000000000000000 : ℚ) else
  if p = (3, 1) then (-6665644827833 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-34734327175409 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (23192460784177 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf499_polynomial_eq :
    lowerPullbackPolynomial 11 2 majorizationTriangle499 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray499 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 2 majorizationTriangle499
    cellMatrix_11_2 cellMatrix_11_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf499_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray499 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf499_kernel {p : ℝ × ℝ} (hp : majorizationTriangle499.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 2 majorizationTriangle499
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray499
    majorizationLeaf499_polynomial_eq majorizationLeaf499_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 500. -/
def majorizationTriangle500 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 500. -/
def majorizationArray500 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9079310566529513076099969288688740543112997641 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (5278661641874470220609050531637947241295683941 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (0, 2) then (1283381071484621 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (160304614248539 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (8461903630326553481817351618415385006030217811 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (-145175746853073 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (46592780842203 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (648650088523 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-2648105834415031 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-93783847657021 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (62680213304591 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-5574941328389 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-214661718235421 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-96022505660437 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-108728001713 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (23192460784177 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf500_polynomial_eq :
    lowerPullbackPolynomial 11 2 majorizationTriangle500 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray500 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 2 majorizationTriangle500
    cellMatrix_11_2 cellMatrix_11_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf500_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray500 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf500_kernel {p : ℝ × ℝ} (hp : majorizationTriangle500.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 2 majorizationTriangle500
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray500
    majorizationLeaf500_polynomial_eq majorizationLeaf500_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 501. -/
def majorizationTriangle501 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 501. -/
def majorizationArray501 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (48735311159445076531306061693807990938381643537 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 1) then (-1023343725586779342933727494493857237094349281 /
    7605903601369376408980219232256000000000000000 : ℚ) else
  if p = (0, 2) then (361700782671621 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-2661499784776141 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-23639245401755826670678588653085554431963244281 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-252367233809961 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-89553900704621 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (189769957608251 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-238563962720871 /
    50000000000000000 : ℚ) else
  if p = (2, 1) then (94903176658729 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (31285742651439 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (25431547970507 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (214661718235421 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-96022505660437 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (108728001713 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-72534472591987 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf501_polynomial_eq :
    lowerPullbackPolynomial 11 3 majorizationTriangle501 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray501 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 3 majorizationTriangle501
    cellMatrix_11_3 cellMatrix_11_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf501_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray501 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf501_kernel {p : ℝ × ℝ} (hp : majorizationTriangle501.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 3 majorizationTriangle501
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray501
    majorizationLeaf501_polynomial_eq majorizationLeaf501_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 502. -/
def majorizationTriangle502 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 502. -/
def majorizationArray502 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1226456401126421624759876438731156409425801 /
    7922816251426433759354395033600000000000000000 : ℚ) else
  if p = (0, 1) then (117414843777416707 /
    1000000000000000000 : ℚ) else
  if p = (0, 2) then (-268349556382411 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (1044214870315927 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (352281257362585931 /
    3000000000000000000 : ℚ) else
  if p = (1, 1) then (-1023707961730117 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (64865323253737 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (84049290478639 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-29677554348689 /
    8000000000000000 : ℚ) else
  if p = (2, 1) then (-172041349644723 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (15577288683111 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1177573115537 /
    15000000000000000 : ℚ) else
  if p = (3, 0) then (72807043666369 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-84169761124499 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (36212872295137 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-72534472591987 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf502_polynomial_eq :
    lowerPullbackPolynomial 11 3 majorizationTriangle502 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray502 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 3 majorizationTriangle502
    cellMatrix_11_3 cellMatrix_11_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf502_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray502 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf502_kernel {p : ℝ × ℝ} (hp : majorizationTriangle502.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 3 majorizationTriangle502
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray502
    majorizationLeaf502_polynomial_eq majorizationLeaf502_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 503. -/
def majorizationTriangle503 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 503. -/
def majorizationArray503 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (40627322262400945125938603769700728713341799189 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-333466594050382531 /
    3000000000000000000 : ℚ) else
  if p = (0, 2) then (-98259017749283 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-364766905333229 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-110250387345910957 /
    1000000000000000000 : ℚ) else
  if p = (1, 1) then (-1536130183268561 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-168445645210233 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (104862525874067 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-2080202488818937 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (340380871893721 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (17600606654677 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-3481756370823 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (-72807043666369 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-84169761124499 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-36212872295137 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1399320948103 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf503_polynomial_eq :
    lowerPullbackPolynomial 11 4 majorizationTriangle503 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray503 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 4 majorizationTriangle503
    cellMatrix_11_4 cellMatrix_11_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf503_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray503 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf503_kernel {p : ℝ × ℝ} (hp : majorizationTriangle503.Contains p) :
    (1 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 4 majorizationTriangle503
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray503
    majorizationLeaf503_polynomial_eq majorizationLeaf503_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 504. -/
def majorizationTriangle504 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 504. -/
def majorizationArray504 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (10561750757261028448327641929335585711776526201 /
    11884224377139650639031592550400000000000000000 : ℚ) else
  if p = (0, 1) then (34028892812738056634081828583026869252102949091 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-109469175652983 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (826342200147419 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (100434001761169727645540482026641703375791594153 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-231627967590711 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-16206141462101 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (75642245958249 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-283065859225547 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-41940358206459 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-9928602750999 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (11811498061703 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (425559018236659 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-29639916005231 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (27816946606519 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1399320948103 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf504_polynomial_eq :
    lowerPullbackPolynomial 11 4 majorizationTriangle504 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray504 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 4 majorizationTriangle504
    cellMatrix_11_4 cellMatrix_11_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf504_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray504 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf504_kernel {p : ℝ × ℝ} (hp : majorizationTriangle504.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 4 majorizationTriangle504
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray504
    majorizationLeaf504_polynomial_eq majorizationLeaf504_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 505. -/
def majorizationTriangle505 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 505. -/
def majorizationArray505 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2829397193745500459359651778046444133908807602539 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-96415179435776637184002257119417246578823535273 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-943549309186369 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-311459752430957 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-32133407676049852510429075239166354883236727011 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-779216948033413 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (2283467693937 /
    3125000000000000 : ℚ) else
  if p = (1, 3) then (87819842036093 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-211819279719991 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (232080296439073 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (111802149097 /
    625000000000000 : ℚ) else
  if p = (2, 3) then (-3314385015361 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-425559018236659 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-29639916005231 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (-27816946606519 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (29245856223193 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf505_polynomial_eq :
    lowerPullbackPolynomial 11 5 majorizationTriangle505 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray505 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 5 majorizationTriangle505
    cellMatrix_11_5 cellMatrix_11_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf505_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray505 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf505_kernel {p : ℝ × ℝ} (hp : majorizationTriangle505.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 5 majorizationTriangle505
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray505
    majorizationLeaf505_polynomial_eq majorizationLeaf505_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 506. -/
def majorizationTriangle506 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 506. -/
def majorizationArray506 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (55809923868704660569533217560058856521096522379 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (50143950427890380332530285774487233052903625609 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-1977789304844569 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (10492239689057 /
    28125000000000000 : ℚ) else
  if p = (1, 0) then (45321754053084155560681332576550354869787972489 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-63151206619213 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-25924080278813 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (404914117363 /
    2500000000000000 : ℚ) else
  if p = (2, 0) then (-617689886102329 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-2946994459979 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (-69313040611 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-1930270117711 /
    60000000000000000 : ℚ) else
  if p = (3, 0) then (1877971340046169 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-378421090255193 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (5277607397969 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (29245856223193 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf506_polynomial_eq :
    lowerPullbackPolynomial 11 5 majorizationTriangle506 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray506 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 5 majorizationTriangle506
    cellMatrix_11_5 cellMatrix_11_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf506_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray506 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf506_kernel {p : ℝ × ℝ} (hp : majorizationTriangle506.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 5 majorizationTriangle506
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray506
    majorizationLeaf506_polynomial_eq majorizationLeaf506_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
