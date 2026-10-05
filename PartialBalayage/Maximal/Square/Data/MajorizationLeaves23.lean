/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices23

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

/-- The actual closed rational triangle of majorization leaf 667. -/
def majorizationTriangle667 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 667. -/
def majorizationArray667 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1216512559820224825807871221354237516955677635703 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-72385100112268019538112148252827091347878011101 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1591962249196889 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-544936894530629 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-76385382643809214161703084803227726826038190301 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-586715984761903 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (43851280159547 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-63730214294191 /
    18750000000000000 : ℚ) else
  if p = (2, 0) then (-586771858388707 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (18204536881661 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (205684379451307 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-1472670259390709 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-1016206233652319 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-2032922391501959 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-2898571892716451 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (6920517142425991 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf667_polynomial_eq :
    lowerPullbackPolynomial 16 6 majorizationTriangle667 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray667 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 6 majorizationTriangle667
    cellMatrix_16_6 cellMatrix_16_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf667_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray667 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf667_kernel {p : ℝ × ℝ} (hp : majorizationTriangle667.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 6 majorizationTriangle667
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray667
    majorizationLeaf667_polynomial_eq majorizationLeaf667_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 668. -/
def majorizationTriangle668 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 668. -/
def majorizationArray668 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (17854645572599284234751972756903924632155975203 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (7822608046511636412692207621606703939345983521 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (-6788244066240971 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (1101480816397933 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (23813026954323346786100880531280286893698218083 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-239762690561669 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-784570915056581 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (2955493194937517 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-1183749851158801 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-3924774180704253 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (8408490632256727 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-2723923441517641 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (218850533495063 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (6010968107917121 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-3647487464045177 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (6920517142425991 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf668_polynomial_eq :
    lowerPullbackPolynomial 16 6 majorizationTriangle668 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray668 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 6 majorizationTriangle668
    cellMatrix_16_6 cellMatrix_16_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf668_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray668 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf668_kernel {p : ℝ × ℝ} (hp : majorizationTriangle668.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 6 majorizationTriangle668
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray668
    majorizationLeaf668_polynomial_eq majorizationLeaf668_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 669. -/
def majorizationTriangle669 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 669. -/
def majorizationArray669 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (243731822823708068322274163548742754042949973639 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-19760027424885330467918630522894126046043469923 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-1068449571863759 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-1805506749411679 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-19903971328664675063462650938302528253826463843 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-303739370629973 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (-975832148547509 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (5892668179407151 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1974547227169219 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-521548481803217 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-633492939969701 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (10955097906420617 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-218850533495063 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (6010968107917121 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (3647487464045177 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-14654490018481601 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf669_polynomial_eq :
    lowerPullbackPolynomial 16 7 majorizationTriangle669 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray669 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 7 majorizationTriangle669
    cellMatrix_16_7 cellMatrix_16_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf669_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray669 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf669_kernel {p : ℝ × ℝ} (hp : majorizationTriangle669.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 7 majorizationTriangle669
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray669
    majorizationLeaf669_polynomial_eq majorizationLeaf669_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 670. -/
def majorizationTriangle670 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 670. -/
def majorizationArray670 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5475156139109382224387261170173677254511469293 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (26693511040689496240651939576433104520202343923 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (3160141851216863 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-19428811471108423 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (80172010642699578163523130618177494736436494809 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (642597456630331 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-302092316321011 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-1506116044714817 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (254543261050927 /
    12000000000000000 : ℚ) else
  if p = (2, 1) then (-1193936657337561 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-4972695749142929 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (3670776426108517 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-19581656661739187 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1413087144775019 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (18366517644827671 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-14654490018481601 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf670_polynomial_eq :
    lowerPullbackPolynomial 16 7 majorizationTriangle670 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray670 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 7 majorizationTriangle670
    cellMatrix_16_7 cellMatrix_16_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf670_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray670 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf670_kernel {p : ℝ × ℝ} (hp : majorizationTriangle670.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 7 majorizationTriangle670
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray670
    majorizationLeaf670_polynomial_eq majorizationLeaf670_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 671. -/
def majorizationTriangle671 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 671. -/
def majorizationArray671 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (236000378030438098943160910618076476244083702409 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-90927869808771272256352088425771762983569228249 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-405287002457781 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (2384463700957843 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-29825875607903635470675355806002120147899700723 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-209610824216523 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (3941003882312133 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-60745736196223 /
    20000000000000000 : ℚ) else
  if p = (2, 0) then (-2284831203064279 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (3800960459450141 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (8421126146541813 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-2262159515822249 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (19581656661739187 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1413087144775019 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-18366517644827671 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (15910713358334609 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf671_polynomial_eq :
    lowerPullbackPolynomial 16 8 majorizationTriangle671 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray671 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 8 majorizationTriangle671
    cellMatrix_16_8 cellMatrix_16_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf671_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray671 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf671_kernel {p : ℝ × ℝ} (hp : majorizationTriangle671.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 8 majorizationTriangle671
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray671
    majorizationLeaf671_polynomial_eq majorizationLeaf671_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 672. -/
def majorizationTriangle672 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 672. -/
def majorizationArray672 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1249521200512825260691867325178418302236948213 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (25044393334794789208524362210020235550080176967 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (738484026088507 /
    150000000000000000 : ℚ) else
  if p = (1, 0) then (25044393334794789208524362210020235550080176967 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (472344886475671 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (472344886475671 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-387218601398341 /
    37500000000000000 : ℚ) else
  if p = (2, 0) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (472344886475671 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (472344886475671 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-2287358431681871 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (176349577564437 /
    40000000000000000 : ℚ) else
  if p = (3, 1) then (-2108231905920381 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-4484969690613849 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (15910713358334609 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf672_polynomial_eq :
    lowerPullbackPolynomial 16 8 majorizationTriangle672 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray672 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 8 majorizationTriangle672
    cellMatrix_16_8 cellMatrix_16_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf672_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray672 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf672_kernel {p : ℝ × ℝ} (hp : majorizationTriangle672.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 8 majorizationTriangle672
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray672
    majorizationLeaf672_polynomial_eq majorizationLeaf672_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 673. -/
def majorizationTriangle673 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 673. -/
def majorizationArray673 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (215354158084269867428796100407207429692551836041 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-37996501498662850100470238484271996737266455367 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (12996404570796029 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-9431297893755827 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-12439803323039888948698596802177543426998208109 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (5011581557654961 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2118631796425443 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-378915898231043 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (11714490082205033 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (101837465038231 /
    8000000000000000 : ℚ) else
  if p = (2, 2) then (-9676149980036179 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (13241256657076381 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-176349577564437 /
    40000000000000000 : ℚ) else
  if p = (3, 1) then (-2108231905920381 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (4484969690613849 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-1891112860986861 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf673_polynomial_eq :
    lowerPullbackPolynomial 16 9 majorizationTriangle673 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray673 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 9 majorizationTriangle673
    cellMatrix_16_9 cellMatrix_16_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf673_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray673 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf673_kernel {p : ℝ × ℝ} (hp : majorizationTriangle673.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 9 majorizationTriangle673
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray673
    majorizationLeaf673_polynomial_eq majorizationLeaf673_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 674. -/
def majorizationTriangle674 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 674. -/
def majorizationArray674 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (472344886475671 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (2, 3) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (198061482057789 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-1891112860986861 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf674_polynomial_eq :
    lowerPullbackPolynomial 16 9 majorizationTriangle674 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray674 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 9 majorizationTriangle674
    cellMatrix_16_9 cellMatrix_16_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf674_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray674 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf674_kernel {p : ℝ × ℝ} (hp : majorizationTriangle674.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 9 majorizationTriangle674
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray674
    majorizationLeaf674_polynomial_eq majorizationLeaf674_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 675. -/
def majorizationTriangle675 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 675. -/
def majorizationArray675 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (27155679569130358744752072774100324529796372073 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-15412157608644748050327014610978056495588665593 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-198061482057789 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (-15412157608644748050327014610978056495588665593 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-594184446173367 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-198061482057789 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-594184446173367 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (198061482057789 /
    100000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf675_polynomial_eq :
    lowerPullbackPolynomial 16 10 majorizationTriangle675 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray675 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 10 majorizationTriangle675
    cellMatrix_16_10 cellMatrix_16_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf675_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray675 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf675_kernel {p : ℝ × ℝ} (hp : majorizationTriangle675.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 10 majorizationTriangle675
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray675
    majorizationLeaf675_polynomial_eq majorizationLeaf675_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 676. -/
def majorizationTriangle676 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 676. -/
def majorizationArray676 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (198061482057789 /
    100000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf676_polynomial_eq :
    lowerPullbackPolynomial 16 10 majorizationTriangle676 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray676 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 10 majorizationTriangle676
    cellMatrix_16_10 cellMatrix_16_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf676_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray676 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf676_kernel {p : ℝ × ℝ} (hp : majorizationTriangle676.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 10 majorizationTriangle676
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray676
    majorizationLeaf676_polynomial_eq majorizationLeaf676_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 677. -/
def majorizationTriangle677 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 677. -/
def majorizationArray677 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf677_polynomial_eq :
    lowerPullbackPolynomial 16 11 majorizationTriangle677 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray677 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 11 majorizationTriangle677
    cellMatrix_16_11 cellMatrix_16_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf677_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray677 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf677_kernel {p : ℝ × ℝ} (hp : majorizationTriangle677.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 11 majorizationTriangle677
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray677
    majorizationLeaf677_polynomial_eq majorizationLeaf677_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
