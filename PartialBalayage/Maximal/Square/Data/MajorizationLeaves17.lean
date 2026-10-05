/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices17

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

/-- The actual closed rational triangle of majorization leaf 596. -/
def majorizationTriangle596 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 596. -/
def majorizationArray596 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (463164358334309700551818447841470074685123227547 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-85602068611395631854823933134756903764832322009 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (1782692882853139 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (695898291560869 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (8666278691317376047941314611808950252691226151 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (2690797257730491 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (3564909796864153 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1862668503855563 /
    37500000000000000 : ℚ) else
  if p = (2, 0) then (-6436765676996479 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-6176632832493097 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2443921653858613 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (5761089151880057 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (46960440884531 /
    4687500000000000 : ℚ) else
  if p = (3, 1) then (1583157541754183 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (701279057563667 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (-475905318063229 /
    25000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf596_polynomial_eq :
    lowerPullbackPolynomial 13 11 majorizationTriangle596 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray596 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 11 majorizationTriangle596
    cellMatrix_13_11 cellMatrix_13_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf596_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray596 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf596_kernel {p : ℝ × ℝ} (hp : majorizationTriangle596.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 11 majorizationTriangle596
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray596
    majorizationLeaf596_polynomial_eq majorizationLeaf596_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 597. -/
def majorizationTriangle597 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 597. -/
def majorizationArray597 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6055963178805141205792689051661544315254133449 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (21211536859615087255191410725409291631468024647 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (219420508366851 /
    25000000000000000 : ℚ) else
  if p = (1, 0) then (21211536859615087255191410725409291631468024647 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-529492956971297 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-529492956971297 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1266297715079797 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-529492956971297 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-529492956971297 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-50225335121309 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-3139355484668051 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (-32058202029653 /
    12000000000000000 : ℚ) else
  if p = (3, 2) then (2154152850815707 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (-475905318063229 /
    25000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf597_polynomial_eq :
    lowerPullbackPolynomial 13 11 majorizationTriangle597 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray597 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 11 majorizationTriangle597
    cellMatrix_13_11 cellMatrix_13_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf597_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray597 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf597_kernel {p : ℝ × ℝ} (hp : majorizationTriangle597.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 11 majorizationTriangle597
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray597
    majorizationLeaf597_polynomial_eq majorizationLeaf597_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 598. -/
def majorizationTriangle598 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 598. -/
def majorizationArray598 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (137466262936964330974591171618314446712571670921 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-14907490154045218754480067065293209330350625607 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (9218466406095163 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-32163304967825893 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (8412353092489020598259110814638859008178977171 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-149370870103451 /
    6250000000000000 : ℚ) else
  if p = (1, 2) then (-11336438233980351 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (36399248623596269 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-7195923079745939 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (665474003856311 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (2479084829584589 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (-38517220451481457 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (3139355484668051 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (-32058202029653 /
    12000000000000000 : ℚ) else
  if p = (3, 2) then (-2154152850815707 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (39576206365424051 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf598_polynomial_eq :
    lowerPullbackPolynomial 13 12 majorizationTriangle598 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray598 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 12 majorizationTriangle598
    cellMatrix_13_12 cellMatrix_13_12_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf598_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray598 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf598_kernel {p : ℝ × ℝ} (hp : majorizationTriangle598.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((12 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 12 majorizationTriangle598
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray598
    majorizationLeaf598_polynomial_eq majorizationLeaf598_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 599. -/
def majorizationTriangle599 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 599. -/
def majorizationArray599 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (-529492956971297 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (2, 3) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-13726372155635567 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (39576206365424051 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf599_polynomial_eq :
    lowerPullbackPolynomial 13 12 majorizationTriangle599 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray599 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 12 majorizationTriangle599
    cellMatrix_13_12 cellMatrix_13_12_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf599_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray599 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf599_kernel {p : ℝ × ℝ} (hp : majorizationTriangle599.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((12 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 12 majorizationTriangle599
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray599
    majorizationLeaf599_polynomial_eq majorizationLeaf599_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 600. -/
def majorizationTriangle600 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 600. -/
def majorizationArray600 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (217001674220829276148661276281945822981635180977 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-18837030924590291596873665147977071700233829099 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (13726372155635567 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-18837030924590291596873665147977071700233829099 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (13726372155635567 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-13726372155635567 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf600_polynomial_eq :
    lowerPullbackPolynomial 13 13 majorizationTriangle600 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray600 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 13 majorizationTriangle600
    cellMatrix_13_13 cellMatrix_13_13_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf600_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray600 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf600_kernel {p : ℝ × ℝ} (hp : majorizationTriangle600.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((13 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 13 majorizationTriangle600
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray600
    majorizationLeaf600_polynomial_eq majorizationLeaf600_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 601. -/
def majorizationTriangle601 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 601. -/
def majorizationArray601 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (-13726372155635567 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf601_polynomial_eq :
    lowerPullbackPolynomial 13 13 majorizationTriangle601 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray601 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 13 majorizationTriangle601
    cellMatrix_13_13 cellMatrix_13_13_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf601_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray601 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf601_kernel {p : ℝ × ℝ} (hp : majorizationTriangle601.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((13 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 13 majorizationTriangle601
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray601
    majorizationLeaf601_polynomial_eq majorizationLeaf601_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 603. -/
def majorizationTriangle603 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 603. -/
def majorizationArray603 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (167674837245404588694974587969931516690892770611 /
    570442770102703230673516442419200000000000000000 : ℚ) else
  if p = (0, 2) then (-5770728585157 /
    18750000000000000 : ℚ) else
  if p = (0, 3) then (433037730133069 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-9309001600989353152620157046182795947399733843 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 2) then (16698444207453 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-91899345405639 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-465286015279133 /
    150000000000000000 : ℚ) else
  if p = (2, 2) then (-157285556983 /
    625000000000000 : ℚ) else
  if p = (2, 3) then (61926667917587 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (20324411027879 /
    90000000000000000 : ℚ) else
  if p = (3, 2) then (-669769880291 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (607827806703 /
    100000000000000000 : ℚ) else
  if p = (0, 1) then (-9860496808232332253696681791512031373203104339 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf603_polynomial_eq :
    lowerPullbackPolynomial 14 0 majorizationTriangle603 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray603 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 0 majorizationTriangle603
    cellMatrix_14_0 cellMatrix_14_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf603_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray603 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf603_kernel {p : ℝ × ℝ} (hp : majorizationTriangle603.Contains p) :
    (1 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 0 majorizationTriangle603
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray603
    majorizationLeaf603_polynomial_eq majorizationLeaf603_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 604. -/
def majorizationTriangle604 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 604. -/
def majorizationArray604 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (16237690791252538461936062663785269739592657 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (132212833653339197 /
    1000000000000000000 : ℚ) else
  if p = (0, 2) then (1597241578317013 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1534815446288009 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (395663491749745681 /
    3000000000000000000 : ℚ) else
  if p = (1, 1) then (-80412364522409 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (110658082191749 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-140903799861089 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1540819645387883 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (33153347073207 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (19857110682517 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-72867568438241 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-204695941257371 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (2791370739163 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-826182099949 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (607827806703 /
    100000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf604_polynomial_eq :
    lowerPullbackPolynomial 14 0 majorizationTriangle604 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray604 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 0 majorizationTriangle604
    cellMatrix_14_0 cellMatrix_14_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf604_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray604 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf604_kernel {p : ℝ × ℝ} (hp : majorizationTriangle604.Contains p) :
    (1 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 0 majorizationTriangle604
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray604
    majorizationLeaf604_polynomial_eq majorizationLeaf604_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 605. -/
def majorizationTriangle605 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 605. -/
def majorizationArray605 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5122896095099667255933142061677981006965415341 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 1) then (-395957529405671191 /
    3000000000000000000 : ℚ) else
  if p = (0, 2) then (660175111980107 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-94004038453899 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-126069445294431047 /
    1000000000000000000 : ℚ) else
  if p = (1, 1) then (-8522928897669 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-142110482557293 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-4018554405259 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-5200564074407 /
    1600000000000000 : ℚ) else
  if p = (2, 1) then (-38736088551533 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (11595289683027 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-98806889701 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (204695941257371 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (2791370739163 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (826182099949 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (-6957010121449 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf605_polynomial_eq :
    lowerPullbackPolynomial 14 1 majorizationTriangle605 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray605 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 1 majorizationTriangle605
    cellMatrix_14_1 cellMatrix_14_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf605_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray605 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf605_kernel {p : ℝ × ℝ} (hp : majorizationTriangle605.Contains p) :
    (1 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 1 majorizationTriangle605
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray605
    majorizationLeaf605_polynomial_eq majorizationLeaf605_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 606. -/
def majorizationTriangle606 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 606. -/
def majorizationArray606 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (31334615404637786409395155633854950959289257579 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (106014170857156656423045555114971666915027720873 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (713832228615253 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (460109036303 /
    937500000000000 : ℚ) else
  if p = (1, 0) then (36773215482075769018519663027395864592368666851 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-329582320366543 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (27702374730477 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-6963447865159 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-320612297653963 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (3158451883607 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-499204605469 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (3725522284977 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-430054539583843 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1235353112959 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (12609209364857 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-6957010121449 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf606_polynomial_eq :
    lowerPullbackPolynomial 14 1 majorizationTriangle606 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray606 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 1 majorizationTriangle606
    cellMatrix_14_1 cellMatrix_14_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf606_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray606 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf606_kernel {p : ℝ × ℝ} (hp : majorizationTriangle606.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 1 majorizationTriangle606
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray606
    majorizationLeaf606_polynomial_eq majorizationLeaf606_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 607. -/
def majorizationTriangle607 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 607. -/
def majorizationArray607 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (943142088707960651909661612945038953901594570873 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-104524467755649218583914219760524979384589884073 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (37816299661841 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (-413814477700039 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-104557893182664416004590952691682163825989261993 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-148381224208757 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-18266129620319 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (1801315623551 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-338852671308943 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-8513806265497 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (1264148292189 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-99016490659 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (430054539583843 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1235353112959 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-12609209364857 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (234338861543 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf607_polynomial_eq :
    lowerPullbackPolynomial 14 2 majorizationTriangle607 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray607 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 2 majorizationTriangle607
    cellMatrix_14_2 cellMatrix_14_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf607_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray607 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf607_kernel {p : ℝ × ℝ} (hp : majorizationTriangle607.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 2 majorizationTriangle607
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray607
    majorizationLeaf607_polynomial_eq majorizationLeaf607_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 608. -/
def majorizationTriangle608 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 608. -/
def majorizationArray608 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (11057088327515374481172371800131006034691757391 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (45848096595539313050615488017727943688843056009 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-52760099392391 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (63882694000637 /
    150000000000000000 : ℚ) else
  if p = (1, 0) then (16538911390900980746542564211431279538098980483 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-580803620824627 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (112709426805699 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (4300407807781 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-1649344913069507 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (12202882936277 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (6085399509103 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-11173727261 /
    781250000000000 : ℚ) else
  if p = (3, 0) then (-45034058365541 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-2921902231007 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (1078551634379 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (234338861543 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf608_polynomial_eq :
    lowerPullbackPolynomial 14 2 majorizationTriangle608 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray608 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 2 majorizationTriangle608
    cellMatrix_14_2 cellMatrix_14_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf608_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray608 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf608_kernel {p : ℝ × ℝ} (hp : majorizationTriangle608.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 2 majorizationTriangle608
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray608
    majorizationLeaf608_polynomial_eq majorizationLeaf608_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
