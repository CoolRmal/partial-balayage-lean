/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices20

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

/-- The actual closed rational triangle of majorization leaf 632. -/
def majorizationTriangle632 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 632. -/
def majorizationArray632 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2829604899881987639874421835418590802846304096619 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-36558737826772813035194542740205737926475516131 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (1597241578317013 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-460109036303 /
    937500000000000 : ℚ) else
  if p = (1, 0) then (-109367220727661129444793595404007441259043101353 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-80412364522409 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-110658082191749 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-6963447865159 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-1540819645387883 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-33153347073207 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (19857110682517 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3725522284977 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (174932026323487 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (2511862871171 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (-7566150429389 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (79194782576389 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf632_polynomial_eq :
    lowerPullbackPolynomial 15 1 majorizationTriangle632 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray632 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 1 majorizationTriangle632
    cellMatrix_15_1 cellMatrix_15_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf632_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray632 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf632_kernel {p : ℝ × ℝ} (hp : majorizationTriangle632.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 1 majorizationTriangle632
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray632
    majorizationLeaf632_polynomial_eq majorizationLeaf632_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 633. -/
def majorizationTriangle633 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 633. -/
def majorizationArray633 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2189213698827366214121878392085379472559965251 /
    2852213850513516153367582212096000000000000000 : ℚ) else
  if p = (0, 1) then (15735340149597790364478139169202787295098619523 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (15473705885867 /
    30000000000000000 : ℚ) else
  if p = (0, 3) then (190967068527373 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (50808972025026522319664443526437511559838061449 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-188955917392369 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (62419170282899 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (2211574565343 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-640117188608329 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (203357843751 /
    1250000000000000 : ℚ) else
  if p = (2, 2) then (4042389028483 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-56841648866527 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-107609037017719 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-133959964657 /
    4800000000000000 : ℚ) else
  if p = (3, 2) then (-6221859713759 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (79194782576389 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf633_polynomial_eq :
    lowerPullbackPolynomial 15 1 majorizationTriangle633 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray633 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 1 majorizationTriangle633
    cellMatrix_15_1 cellMatrix_15_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf633_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray633 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf633_kernel {p : ℝ × ℝ} (hp : majorizationTriangle633.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 1 majorizationTriangle633
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray633
    majorizationLeaf633_polynomial_eq majorizationLeaf633_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 634. -/
def majorizationTriangle634 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 634. -/
def majorizationArray634 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1243735076981743292989036177230636588832939789687 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-46371851896416509703375416164812565460880872329 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (713832228615253 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-63882694000637 /
    150000000000000000 : ℚ) else
  if p = (1, 0) then (-16174863230317278339877377716140176297306670723 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-329582320366543 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-27702374730477 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (4300407807781 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-320612297653963 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-3158451883607 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-499204605469 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (11173727261 /
    781250000000000 : ℚ) else
  if p = (3, 0) then (107609037017719 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-133959964657 /
    4800000000000000 : ℚ) else
  if p = (3, 2) then (6221859713759 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-7237885386167 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf634_polynomial_eq :
    lowerPullbackPolynomial 15 2 majorizationTriangle634 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray634 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 2 majorizationTriangle634
    cellMatrix_15_2 cellMatrix_15_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf634_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray634 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf634_kernel {p : ℝ × ℝ} (hp : majorizationTriangle634.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 2 majorizationTriangle634
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray634
    majorizationLeaf634_polynomial_eq majorizationLeaf634_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 635. -/
def majorizationTriangle635 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 635. -/
def majorizationArray635 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (48086714008240696985014433085207555747754359419 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (83444916335081590682034748764730573356851082023 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-24837119653619 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (19635223115979 /
    50000000000000000 : ℚ) else
  if p = (1, 0) then (92902155465007706751488823272770421403832365863 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-314025268156877 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (62650180481609 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-7700339957 /
    10000000000000000 : ℚ) else
  if p = (2, 0) then (-170522920456987 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (700880651057 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (-9338166833311 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (5807648296759 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-95053849804537 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-22841149616573 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (330156442343 /
    8000000000000000 : ℚ) else
  if p = (3, 3) then (-7237885386167 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf635_polynomial_eq :
    lowerPullbackPolynomial 15 2 majorizationTriangle635 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray635 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 2 majorizationTriangle635
    cellMatrix_15_2 cellMatrix_15_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf635_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray635 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf635_kernel {p : ℝ × ℝ} (hp : majorizationTriangle635.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 2 majorizationTriangle635
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray635
    majorizationLeaf635_polynomial_eq majorizationLeaf635_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 636. -/
def majorizationTriangle636 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 636. -/
def majorizationArray636 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2195238265738956674137870324868662097606488145069 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-80589754149685824744486626386245726294092886823 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-52760099392391 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-151718241137083 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-29375676434671027707503678539792505381666885901 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-580803620824627 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-112709426805699 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (677415324759 /
    10000000000000000 : ℚ) else
  if p = (2, 0) then (-1649344913069507 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-12202882936277 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (6085399509103 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3476915586793 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (95053849804537 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-22841149616573 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-330156442343 /
    8000000000000000 : ℚ) else
  if p = (3, 3) then (725004723223 /
    25000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf636_polynomial_eq :
    lowerPullbackPolynomial 15 3 majorizationTriangle636 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray636 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 3 majorizationTriangle636
    cellMatrix_15_3 cellMatrix_15_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf636_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray636 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf636_kernel {p : ℝ × ℝ} (hp : majorizationTriangle636.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 3 majorizationTriangle636
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray636
    majorizationLeaf636_polynomial_eq majorizationLeaf636_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 637. -/
def majorizationTriangle637 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 637. -/
def majorizationArray637 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (42098115663966054576377415215075852020909424923 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (9637605557784917537119135807809855216884345377 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-380112679777231 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (56152840232551 /
    90000000000000000 : ℚ) else
  if p = (1, 0) then (10880170625204358960836391800326513502059457057 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-420718324035641 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (8808575079431 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (9303652542227 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-7504797234683 /
    3000000000000000 : ℚ) else
  if p = (2, 1) then (24005842254191 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (570868171109 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (-1524063461107 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (-64851080369591 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-20164275895967 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-9146202298777 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (725004723223 /
    25000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf637_polynomial_eq :
    lowerPullbackPolynomial 15 3 majorizationTriangle637 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray637 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 3 majorizationTriangle637
    cellMatrix_15_3 cellMatrix_15_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf637_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray637 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf637_kernel {p : ℝ × ℝ} (hp : majorizationTriangle637.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 3 majorizationTriangle637
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray637
    majorizationLeaf637_polynomial_eq majorizationLeaf637_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 638. -/
def majorizationTriangle638 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 638. -/
def majorizationArray638 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (121100334006756821740549157951434229794977759733 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-9162149596795479432795844621318110665416600097 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-253301205697811 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-4025002129967 /
    5625000000000000 : ℚ) else
  if p = (1, 0) then (-3415681363582561946065170975164630275213741579 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (-153115510990097 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-72064507320159 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (11923794270201 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-1695512688045373 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-5569481722483 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-21729925185241 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1138697128327 /
    30000000000000000 : ℚ) else
  if p = (3, 0) then (64851080369591 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-20164275895967 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (9146202298777 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-19481096544863 /
    180000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf638_polynomial_eq :
    lowerPullbackPolynomial 15 4 majorizationTriangle638 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray638 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 4 majorizationTriangle638
    cellMatrix_15_4 cellMatrix_15_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf638_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray638 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf638_kernel {p : ℝ × ℝ} (hp : majorizationTriangle638.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 4 majorizationTriangle638
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray638
    majorizationLeaf638_polynomial_eq majorizationLeaf638_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 639. -/
def majorizationTriangle639 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 639. -/
def majorizationArray639 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (454936402023829876182964037024447753803440671 /
    891316828285473797927369441280000000000000000 : ℚ) else
  if p = (0, 1) then (1579714772551411728122427164753628005522147937 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-680078060395939 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (8332371683853 /
    12500000000000000 : ℚ) else
  if p = (1, 0) then (1741435132005879754884552376821666549067614817 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (1, 1) then (-547664232177123 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (82903032744327 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-9715039336793 /
    75000000000000000 : ℚ) else
  if p = (2, 0) then (-899952739105283 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (52157835992073 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-166328341171 /
    200000000000000 : ℚ) else
  if p = (2, 3) then (5734567429403 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (-4313053732247 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-32019605510387 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (167372358552299 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-19481096544863 /
    180000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf639_polynomial_eq :
    lowerPullbackPolynomial 15 4 majorizationTriangle639 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray639 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 4 majorizationTriangle639
    cellMatrix_15_4 cellMatrix_15_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf639_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray639 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf639_kernel {p : ℝ × ℝ} (hp : majorizationTriangle639.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 4 majorizationTriangle639
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray639
    majorizationLeaf639_polynomial_eq majorizationLeaf639_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 640. -/
def majorizationTriangle640 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 640. -/
def majorizationArray640 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (106123298858038767689014921466175565812031948193 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-4459846288642105689896907256660795329460641571 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-510901342015699 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-577295933821 /
    3750000000000000 : ℚ) else
  if p = (1, 0) then (-1621887221969996887556033132682525467335395937 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (1, 1) then (-838163803969597 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-521741698953 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1809849376841 /
    9375000000000000 : ℚ) else
  if p = (2, 0) then (-1821470746871801 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-48533316416357 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1044017381299 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-34726352358007 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (4313053732247 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-32019605510387 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-167372358552299 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (32752300592569 /
    75000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf640_polynomial_eq :
    lowerPullbackPolynomial 15 5 majorizationTriangle640 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray640 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 5 majorizationTriangle640
    cellMatrix_15_5 cellMatrix_15_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf640_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray640 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf640_kernel {p : ℝ × ℝ} (hp : majorizationTriangle640.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 5 majorizationTriangle640
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray640
    majorizationLeaf640_polynomial_eq majorizationLeaf640_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 641. -/
def majorizationTriangle641 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 641. -/
def majorizationArray641 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7657511420177375888946173117413005804003767947 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (78318586771150673108601898334553895150193240143 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1591962249196889 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (77268709468337 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (82318869302691867732192834884954530628353419343 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-586715984761903 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-43851280159547 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (63377156451937 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-586771858388707 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-18204536881661 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (205684379451307 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-96282850012269 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (174790675429811 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (291212469565123 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-618682855669357 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (32752300592569 /
    75000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf641_polynomial_eq :
    lowerPullbackPolynomial 15 5 majorizationTriangle641 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray641 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 5 majorizationTriangle641
    cellMatrix_15_5 cellMatrix_15_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf641_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray641 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf641_kernel {p : ℝ × ℝ} (hp : majorizationTriangle641.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 5 majorizationTriangle641
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray641
    majorizationLeaf641_polynomial_eq majorizationLeaf641_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 642. -/
def majorizationTriangle642 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 642. -/
def majorizationArray642 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1461278076539982196579622197979571661416519126989 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-24342940793603202670193932888151429676527788741 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-113264350332503 /
    24000000000000000 : ℚ) else
  if p = (0, 3) then (-110250847492351 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-75157619198635709142995643856884722126509860943 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-955037647485327 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-116352101816777 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (1056084407881 /
    2400000000000000 : ℚ) else
  if p = (2, 0) then (-2172296758125017 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-254803395801801 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-207314096766743 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (10030508740579 /
    9375000000000000 : ℚ) else
  if p = (3, 0) then (-174790675429811 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (291212469565123 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (618682855669357 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-1793646539089237 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf642_polynomial_eq :
    lowerPullbackPolynomial 15 6 majorizationTriangle642 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray642 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 6 majorizationTriangle642
    cellMatrix_15_6 cellMatrix_15_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf642_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray642 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf642_kernel {p : ℝ × ℝ} (hp : majorizationTriangle642.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 6 majorizationTriangle642
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray642
    majorizationLeaf642_polynomial_eq majorizationLeaf642_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 643. -/
def majorizationTriangle643 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 643. -/
def majorizationArray643 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6140593101714448317733210292571824230522283651 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (84202333569539259768525899388223531756288041181 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1068449571863759 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (544936894530629 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (84778109184656638150701981049857140587420016861 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-303739370629973 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (975832148547509 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-63730214294191 /
    18750000000000000 : ℚ) else
  if p = (2, 0) then (-1974547227169219 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (521548481803217 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-633492939969701 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (1472670259390709 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (206479555580969 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-2058714897274637 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (2968610222509117 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-1793646539089237 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf643_polynomial_eq :
    lowerPullbackPolynomial 15 6 majorizationTriangle643 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray643 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 6 majorizationTriangle643
    cellMatrix_15_6 cellMatrix_15_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf643_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray643 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf643_kernel {p : ℝ × ℝ} (hp : majorizationTriangle643.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 6 majorizationTriangle643
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray643
    majorizationLeaf643_polynomial_eq majorizationLeaf643_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
