/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices28

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

/-- The actual closed rational triangle of majorization leaf 724. -/
def majorizationTriangle724 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 724. -/
def majorizationArray724 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1142043169048914861159894063608145681398464001143 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-21681474886491720903216407804013511778999760287 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-1964266060635367 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-2062360476756133 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-74794140581560292764114895651797359965795082461 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1047709097943751 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-7937593269959 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-1765747643498639 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1398701861730553 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (29679211194357 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (340198020010361 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-2497624383654619 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-40987831643327 /
    90000000000000000 : ℚ) else
  if p = (3, 1) then (-803479586394647 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-73888774248611 /
    18750000000000000 : ℚ) else
  if p = (3, 3) then (11533651845229537 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf724_polynomial_eq :
    lowerPullbackPolynomial 19 3 majorizationTriangle724 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray724 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 3 majorizationTriangle724
    cellMatrix_19_3 cellMatrix_19_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf724_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray724 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf724_kernel {p : ℝ × ℝ} (hp : majorizationTriangle724.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 3 majorizationTriangle724
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray724
    majorizationLeaf724_polynomial_eq majorizationLeaf724_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 725. -/
def majorizationTriangle725 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 725. -/
def majorizationArray725 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (16969769665992295907937311562867237283689524771 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (20846992894310222282885931526112316761376323683 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-6746001388595591 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (36875830144293 /
    20000000000000000 : ℚ) else
  if p = (1, 0) then (22083087495341068463007485868341701047058724963 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-1270119818491921 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-609784546427407 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (79544257240361 /
    10000000000000000 : ℚ) else
  if p = (2, 0) then (-3986999185642559 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-3410261988089599 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (7011784705629727 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1506004576929153 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (400101544623847 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (5197811120529139 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-611280737951599 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (11533651845229537 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf725_polynomial_eq :
    lowerPullbackPolynomial 19 3 majorizationTriangle725 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray725 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 3 majorizationTriangle725
    cellMatrix_19_3 cellMatrix_19_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf725_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray725 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf725_kernel {p : ℝ × ℝ} (hp : majorizationTriangle725.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 3 majorizationTriangle725
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray725
    majorizationLeaf725_polynomial_eq majorizationLeaf725_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 726. -/
def majorizationTriangle726 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 726. -/
def majorizationArray726 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (231684209507576235987270413335071426701451114119 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-5781262419726395255311164383972371910809888801 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (-8053253074783 /
    1200000000000000 : ℚ) else
  if p = (0, 3) then (-357953766307451 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-6466583651364260383522488272823688062386055201 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-144641633707099 /
    10000000000000000 : ℚ) else
  if p = (1, 2) then (-902717804924217 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1733368627240771 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1393347275885509 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-89377456621977 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (-1078713181822129 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (3280054459478683 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-400101544623847 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (5197811120529139 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (611280737951599 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (-8480288043079907 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf726_polynomial_eq :
    lowerPullbackPolynomial 19 4 majorizationTriangle726 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray726 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 4 majorizationTriangle726
    cellMatrix_19_4 cellMatrix_19_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf726_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray726 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf726_kernel {p : ℝ × ℝ} (hp : majorizationTriangle726.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 4 majorizationTriangle726
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray726
    majorizationLeaf726_polynomial_eq majorizationLeaf726_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 727. -/
def majorizationTriangle727 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 727. -/
def majorizationArray727 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5369517122050050822683691167697015514524066541 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (24723401459641160127920426975712166985677067763 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (1942471673174543 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-2743059959078051 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (76247125001459383622008952485770273558982066649 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (4267294155136839 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-99539649659669 /
    8000000000000000 : ℚ) else
  if p = (1, 3) then (-18681049688177 /
    20000000000000000 : ℚ) else
  if p = (2, 0) then (11678440144711747 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-1833130648545381 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-1717783209034789 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (650029197950153 /
    25000000000000000 : ℚ) else
  if p = (3, 0) then (-548663260209937 /
    60000000000000000 : ℚ) else
  if p = (3, 1) then (-476157717540653 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (677985544165239 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (-8480288043079907 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf727_polynomial_eq :
    lowerPullbackPolynomial 19 4 majorizationTriangle727 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray727 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 4 majorizationTriangle727
    cellMatrix_19_4 cellMatrix_19_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf727_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray727 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf727_kernel {p : ℝ × ℝ} (hp : majorizationTriangle727.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 4 majorizationTriangle727
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray727
    majorizationLeaf727_polynomial_eq majorizationLeaf727_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 728. -/
def majorizationTriangle728 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 728. -/
def majorizationArray728 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (687736676822970683434882383740758455706086043547 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-82723454409896093063200401569569621481220243929 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-7248210434158559 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (1009579659441157 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (-29058609994027076660289380955675710379373549043 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-260719602423307 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (3394670271873879 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-134553819066503 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-4781457661586363 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (3737761518707993 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (7682737014791791 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-354705620185317 /
    12500000000000000 : ℚ) else
  if p = (3, 0) then (548663260209937 /
    60000000000000000 : ℚ) else
  if p = (3, 1) then (-476157717540653 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-677985544165239 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (9664226170794481 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf728_polynomial_eq :
    lowerPullbackPolynomial 19 5 majorizationTriangle728 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray728 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 5 majorizationTriangle728
    cellMatrix_19_5 cellMatrix_19_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf728_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray728 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf728_kernel {p : ℝ × ℝ} (hp : majorizationTriangle728.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 5 majorizationTriangle728
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray728
    majorizationLeaf728_polynomial_eq majorizationLeaf728_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 729. -/
def majorizationTriangle729 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 729. -/
def majorizationArray729 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6231726048679116904721267485917278219963388617 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (24726794257094601233762979410523969725653128007 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (2111488555852811 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (24726794257094601233762979410523969725653128007 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1955461313268669 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-3988936247829409 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (1008475052411499 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-5455258477710641 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-4240341817472569 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (9664226170794481 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf729_polynomial_eq :
    lowerPullbackPolynomial 19 5 majorizationTriangle729 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray729 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 5 majorizationTriangle729
    cellMatrix_19_5 cellMatrix_19_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf729_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray729 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf729_kernel {p : ℝ × ℝ} (hp : majorizationTriangle729.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 5 majorizationTriangle729
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray729
    majorizationLeaf729_polynomial_eq majorizationLeaf729_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 730. -/
def majorizationTriangle730 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 730. -/
def majorizationArray730 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (214034596975563420102681383314937158720270348681 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-36462147104268280546851103603557916658475799367 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (10924223435782267 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-3645669974214367 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-12423415057071323806342201504082474202140444269 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (935683923446441 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (2587347357474861 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-3110115422414197 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (12454168170017773 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (2077365779396359 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-373725310164137 /
    8000000000000000 : ℚ) else
  if p = (2, 3) then (6488008120728479 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-1008475052411499 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-5455258477710641 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (4240341817472569 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-408847723494281 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf730_polynomial_eq :
    lowerPullbackPolynomial 19 6 majorizationTriangle730 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray730 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 6 majorizationTriangle730
    cellMatrix_19_6 cellMatrix_19_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf730_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray730 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf730_kernel {p : ℝ × ℝ} (hp : majorizationTriangle730.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 6 majorizationTriangle730
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray730
    majorizationLeaf730_polynomial_eq majorizationLeaf730_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 731. -/
def majorizationTriangle731 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 731. -/
def majorizationArray731 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (1688946349157141 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (2, 3) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (3632883487353533 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-408847723494281 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf731_polynomial_eq :
    lowerPullbackPolynomial 19 6 majorizationTriangle731 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray731 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 6 majorizationTriangle731
    cellMatrix_19_6 cellMatrix_19_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf731_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray731 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf731_kernel {p : ℝ × ℝ} (hp : majorizationTriangle731.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 6 majorizationTriangle731
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray731
    majorizationLeaf731_polynomial_eq majorizationLeaf731_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 732. -/
def majorizationTriangle732 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 732. -/
def majorizationArray732 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (244508512765017289816520863861124825321421932977 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-46343869468778305264733252727156074040020581099 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-3632883487353533 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-46343869468778305264733252727156074040020581099 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-3632883487353533 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (3632883487353533 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf732_polynomial_eq :
    lowerPullbackPolynomial 19 7 majorizationTriangle732 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray732 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 7 majorizationTriangle732
    cellMatrix_19_7 cellMatrix_19_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf732_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray732 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf732_kernel {p : ℝ × ℝ} (hp : majorizationTriangle732.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 7 majorizationTriangle732
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray732
    majorizationLeaf732_polynomial_eq majorizationLeaf732_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 733. -/
def majorizationTriangle733 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 733. -/
def majorizationArray733 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (3632883487353533 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf733_polynomial_eq :
    lowerPullbackPolynomial 19 7 majorizationTriangle733 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray733 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 7 majorizationTriangle733
    cellMatrix_19_7 cellMatrix_19_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf733_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray733 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf733_kernel {p : ℝ × ℝ} (hp : majorizationTriangle733.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 7 majorizationTriangle733
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray733
    majorizationLeaf733_polynomial_eq majorizationLeaf733_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 734. -/
def majorizationTriangle734 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 734. -/
def majorizationArray734 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf734_polynomial_eq :
    lowerPullbackPolynomial 19 8 majorizationTriangle734 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray734 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 8 majorizationTriangle734
    cellMatrix_19_8 cellMatrix_19_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf734_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray734 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf734_kernel {p : ℝ × ℝ} (hp : majorizationTriangle734.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 8 majorizationTriangle734
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray734
    majorizationLeaf734_polynomial_eq majorizationLeaf734_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
