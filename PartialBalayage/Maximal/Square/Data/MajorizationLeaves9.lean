/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices9

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

/-- The actual closed rational triangle of majorization leaf 441. -/
def majorizationTriangle441 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 441. -/
def majorizationArray441 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2063592431960023386967826535005975314402772827309 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-44478009342113119654242075298687840611287109901 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-1244701510315261 /
    60000000000000000 : ℚ) else
  if p = (0, 3) then (346123588807991 /
    18000000000000000 : ℚ) else
  if p = (1, 0) then (-44478009342113119654242075298687840611287109901 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-6005760043122717 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-3279732741970149 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (3220703253351523 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-1244701510315261 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (-3279732741970149 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2879246474787893 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (7723875993678331 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (346123588807991 /
    18000000000000000 : ℚ) else
  if p = (3, 1) then (3220703253351523 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (7723875993678331 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-16376501113392703 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf441_polynomial_eq :
    lowerPullbackPolynomial 9 9 majorizationTriangle441 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray441 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 9 majorizationTriangle441
    cellMatrix_9_9 cellMatrix_9_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf441_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray441 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf441_kernel {p : ℝ × ℝ} (hp : majorizationTriangle441.Contains p) :
    (0 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 9 majorizationTriangle441
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray441
    majorizationLeaf441_polynomial_eq majorizationLeaf441_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 442. -/
def majorizationTriangle442 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 442. -/
def majorizationArray442 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (26377068018020962549278075201271556129455423771 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (7207117804430898359509681515164129309730262539 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (2466820658330093 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (-9177783618703211 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (7207117804430898359509681515164129309730262539 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (-13174955642117829 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (8957490177241779 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-101908539724989 /
    4000000000000000 : ℚ) else
  if p = (2, 0) then (2466820658330093 /
    37500000000000000 : ℚ) else
  if p = (2, 1) then (8957490177241779 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-20184496714216637 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (1001165049324283 /
    12000000000000000 : ℚ) else
  if p = (3, 0) then (-9177783618703211 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-101908539724989 /
    4000000000000000 : ℚ) else
  if p = (3, 2) then (1001165049324283 /
    12000000000000000 : ℚ) else
  if p = (3, 3) then (-16376501113392703 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf442_polynomial_eq :
    lowerPullbackPolynomial 9 9 majorizationTriangle442 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray442 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 9 majorizationTriangle442
    cellMatrix_9_9 cellMatrix_9_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf442_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray442 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf442_kernel {p : ℝ × ℝ} (hp : majorizationTriangle442.Contains p) :
    (0 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 9 majorizationTriangle442
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray442
    majorizationLeaf442_polynomial_eq majorizationLeaf442_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 460. -/
def majorizationTriangle460 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 460. -/
def majorizationArray460 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (436710594510905854975329498550398258085266750799 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 2) then (-2908642340420527 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (84721999762841 /
    14400000000000000 : ℚ) else
  if p = (1, 0) then (-7787833254989298917266421951938656335273658977 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 2) then (540608485032959 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1490017164047723 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-502497940559579 /
    60000000000000000 : ℚ) else
  if p = (2, 2) then (-154586450589349 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (406191769945483 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (216836527794631 /
    180000000000000000 : ℚ) else
  if p = (3, 2) then (94601750519129 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-680519415137 /
    4687500000000000 : ℚ) else
  if p = (0, 1) then (-3048285817209634618508818991222109438111471819 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf460_polynomial_eq :
    lowerPullbackPolynomial 10 0 majorizationTriangle460 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray460 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 0 majorizationTriangle460
    cellMatrix_10_0 cellMatrix_10_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf460_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray460 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf460_kernel {p : ℝ × ℝ} (hp : majorizationTriangle460.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 0 majorizationTriangle460
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray460
    majorizationLeaf460_polynomial_eq majorizationLeaf460_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 461. -/
def majorizationTriangle461 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 461. -/
def majorizationArray461 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (133554572422142415744761230167401926004779569 /
    198070406285660843983859875840000000000000000 : ℚ) else
  if p = (0, 1) then (240934251942183265710920262997475867831564701649 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (1255168453164887 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-7077454332635797 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (209105119771944035089690659236161318287875444689 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (73039251584839 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (57375682164517 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-62596871971291 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (-40955333513839 /
    8000000000000000 : ℚ) else
  if p = (2, 1) then (19013297149601 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (4980582878487 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-1158978516263 /
    4800000000000000 : ℚ) else
  if p = (3, 0) then (-618664081412119 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (29271886665977 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (1442319087487 /
    12000000000000000 : ℚ) else
  if p = (3, 3) then (-680519415137 /
    4687500000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf461_polynomial_eq :
    lowerPullbackPolynomial 10 0 majorizationTriangle461 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray461 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 0 majorizationTriangle461
    cellMatrix_10_0 cellMatrix_10_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf461_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray461 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf461_kernel {p : ℝ × ℝ} (hp : majorizationTriangle461.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 0 majorizationTriangle461
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray461
    majorizationLeaf461_polynomial_eq majorizationLeaf461_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 462. -/
def majorizationTriangle462 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 462. -/
def majorizationArray462 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2531978281536402799365877835736136930662540800947 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-81102576950996097681457267336760574728036571803 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (4772965289514071 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-31307231740133 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-195449422842854441953437429004539617295013973969 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (672416776084113 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-81760038796361 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-47064363035707 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-5546306339186401 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-212154032411913 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (19403773753357 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-3503465041473 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (618664081412119 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (29271886665977 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-1442319087487 /
    12000000000000000 : ℚ) else
  if p = (3, 3) then (9367411157451 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf462_polynomial_eq :
    lowerPullbackPolynomial 10 1 majorizationTriangle462 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray462 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 1 majorizationTriangle462
    cellMatrix_10_1 cellMatrix_10_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf462_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray462 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf462_kernel {p : ℝ × ℝ} (hp : majorizationTriangle462.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 1 majorizationTriangle462
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray462
    majorizationLeaf462_polynomial_eq majorizationLeaf462_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 463. -/
def majorizationTriangle463 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 463. -/
def majorizationArray463 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2663067099504236293288449426452208298262789269 /
    5942112188569825319515796275200000000000000000 : ℚ) else
  if p = (0, 1) then (95508723460550856815309796192756932913032218117 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (1037645507185301 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (36253824329931 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (84919395540201183740527754952383891770610959877 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-2291741941279 /
    1600000000000000 : ℚ) else
  if p = (1, 2) then (72957117952297 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-259690596463 /
    2000000000000000 : ℚ) else
  if p = (2, 0) then (-213889628154133 /
    40000000000000000 : ℚ) else
  if p = (2, 1) then (-5707129665901 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (3947968787403 /
    8000000000000000 : ℚ) else
  if p = (2, 3) then (-153742302693 /
    1250000000000000 : ℚ) else
  if p = (3, 0) then (-2693877802934209 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (57162338332267 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-12190746042709 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (9367411157451 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf463_polynomial_eq :
    lowerPullbackPolynomial 10 1 majorizationTriangle463 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray463 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 1 majorizationTriangle463
    cellMatrix_10_1 cellMatrix_10_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf463_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray463 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf463_kernel {p : ℝ × ℝ} (hp : majorizationTriangle463.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 1 majorizationTriangle463
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray463
    majorizationLeaf463_polynomial_eq majorizationLeaf463_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 464. -/
def majorizationTriangle464 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 464. -/
def majorizationArray464 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (884134243619195804706571135868481536359875452351 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-94805297935246170459126740434474525467472184837 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (2245600101926437 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-60055669956499 /
    112500000000000000 : ℚ) else
  if p = (1, 0) then (-77701260990703409571441858997982244941354911237 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-143188350493309 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-274996641544463 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-3888601811299 /
    75000000000000000 : ℚ) else
  if p = (2, 0) then (-1475555556311551 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-14313345001381 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (43254236821183 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (7380653581559 /
    60000000000000000 : ℚ) else
  if p = (3, 0) then (2693877802934209 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (57162338332267 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (12190746042709 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-109934270197787 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf464_polynomial_eq :
    lowerPullbackPolynomial 10 2 majorizationTriangle464 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray464 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 2 majorizationTriangle464
    cellMatrix_10_2 cellMatrix_10_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf464_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray464 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf464_kernel {p : ℝ × ℝ} (hp : majorizationTriangle464.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 2 majorizationTriangle464
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray464
    majorizationLeaf464_polynomial_eq majorizationLeaf464_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 465. -/
def majorizationTriangle465 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 465. -/
def majorizationArray465 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6383810606039860347487107281558356311069208711 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (4755042313798601901780264271954451309112625351 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (361700782671621 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (314243941842059 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (4451237979749593010738920723632439356707080391 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-252367233809961 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (89553900704621 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (2189995647667 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-238563962720871 /
    50000000000000000 : ℚ) else
  if p = (2, 1) then (-94903176658729 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (31285742651439 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (12042578127399 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-55840055717227 /
    36000000000000000 : ℚ) else
  if p = (3, 1) then (-14195219890051 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (48871762077539 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-109934270197787 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf465_polynomial_eq :
    lowerPullbackPolynomial 10 2 majorizationTriangle465 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray465 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 2 majorizationTriangle465
    cellMatrix_10_2 cellMatrix_10_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf465_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray465 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf465_kernel {p : ℝ × ℝ} (hp : majorizationTriangle465.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 2 majorizationTriangle465
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray465
    majorizationLeaf465_polynomial_eq majorizationLeaf465_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 466. -/
def majorizationTriangle466 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 466. -/
def majorizationArray466 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (146917913124682120817921369275922613925148672317 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-4575480779573460089690588565611016282622953671 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (353030948454889 /
    60000000000000000 : ℚ) else
  if p = (0, 3) then (-3259694521088423 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-1343156644028529459887220282920687064424481517 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (-708736040827431 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-290551048789659 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (244086369066287 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-2827385169255901 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (5454919827439 /
    5000000000000000 : ℚ) else
  if p = (2, 2) then (40078752364489 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-79747959428543 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (55840055717227 /
    36000000000000000 : ℚ) else
  if p = (3, 1) then (-14195219890051 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-48871762077539 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (2103590147981 /
    36000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf466_polynomial_eq :
    lowerPullbackPolynomial 10 3 majorizationTriangle466 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray466 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 3 majorizationTriangle466
    cellMatrix_10_3 cellMatrix_10_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf466_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray466 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf466_kernel {p : ℝ × ℝ} (hp : majorizationTriangle466.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 3 majorizationTriangle466
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray466
    majorizationLeaf466_polynomial_eq majorizationLeaf466_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 467. -/
def majorizationTriangle467 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 467. -/
def majorizationArray467 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (8834373384195279684067632066870429740828257033 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (25051525446819076049849703589771207695096162041 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (-98259017749283 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (2661499784776141 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (8293138165261120508085767528101780080016777811 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (-1536130183268561 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (168445645210233 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (189769957608251 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-2080202488818937 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-340380871893721 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (17600606654677 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-25431547970507 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-13993224452527 /
    10000000000000000 : ℚ) else
  if p = (3, 1) then (-4945749195467 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (-619665270331 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (2103590147981 /
    36000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf467_polynomial_eq :
    lowerPullbackPolynomial 10 3 majorizationTriangle467 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray467 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 3 majorizationTriangle467
    cellMatrix_10_3 cellMatrix_10_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf467_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray467 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf467_kernel {p : ℝ × ℝ} (hp : majorizationTriangle467.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 3 majorizationTriangle467
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray467
    majorizationLeaf467_polynomial_eq majorizationLeaf467_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 468. -/
def majorizationTriangle468 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 468. -/
def majorizationArray468 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (142537269738814796960132073331788847526541970739 /
    570442770102703230673516442419200000000000000000 : ℚ) else
  if p = (0, 1) then (-4645967656228654549265474440988518947347931493 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (0, 2) then (270614963460467 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1474381461573817 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-22762696157072731976183236236463288071912498937 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-2335589907747211 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-337015728513031 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (152946911971881 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-4598982890273797 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (459078852584929 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (80567050029413 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-30675604243699 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (13993224452527 /
    10000000000000000 : ℚ) else
  if p = (3, 1) then (-4945749195467 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (619665270331 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (829176399349 /
    37500000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf468_polynomial_eq :
    lowerPullbackPolynomial 10 4 majorizationTriangle468 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray468 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 4 majorizationTriangle468
    cellMatrix_10_4 cellMatrix_10_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf468_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray468 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf468_kernel {p : ℝ × ℝ} (hp : majorizationTriangle468.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 4 majorizationTriangle468
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray468
    majorizationLeaf468_polynomial_eq majorizationLeaf468_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 469. -/
def majorizationTriangle469 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 469. -/
def majorizationArray469 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2209007475814605118536925672023709260436061 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (177397027838920993 /
    1500000000000000000 : ℚ) else
  if p = (0, 2) then (-943549309186369 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (364766905333229 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (1847639904045853 /
    15625000000000000 : ℚ) else
  if p = (1, 1) then (-779216948033413 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-2283467693937 /
    3125000000000000 : ℚ) else
  if p = (1, 3) then (104862525874067 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-211819279719991 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-232080296439073 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (111802149097 /
    625000000000000 : ℚ) else
  if p = (2, 3) then (3481756370823 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (-46349893255873 /
    37500000000000000 : ℚ) else
  if p = (3, 1) then (-1333865563219 /
    12500000000000000 : ℚ) else
  if p = (3, 2) then (-3936370867727 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (829176399349 /
    37500000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf469_polynomial_eq :
    lowerPullbackPolynomial 10 4 majorizationTriangle469 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray469 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 4 majorizationTriangle469
    cellMatrix_10_4 cellMatrix_10_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf469_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray469 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf469_kernel {p : ℝ × ℝ} (hp : majorizationTriangle469.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 4 majorizationTriangle469
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray469
    majorizationLeaf469_polynomial_eq majorizationLeaf469_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
