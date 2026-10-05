/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices25

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

/-- The actual closed rational triangle of majorization leaf 690. -/
def majorizationTriangle690 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 690. -/
def majorizationArray690 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (80585103198292438904733180950134412594612638253 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 1) then (-18962306110147806988396670714087790753364342883 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-305685495563007 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-1101480816397933 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-6689301567600195410287641333308181106422458401 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-3133536213499121 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1988131814592129 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (2955493194937517 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-1121097889069049 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-1996513317738637 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2487203133813837 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (2723923441517641 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-2053217543234201 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (5862065002275439 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (10690110663805963 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-28897157387186039 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf690_polynomial_eq :
    lowerPullbackPolynomial 17 6 majorizationTriangle690 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray690 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 6 majorizationTriangle690
    cellMatrix_17_6 cellMatrix_17_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf690_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray690 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf690_kernel {p : ℝ × ℝ} (hp : majorizationTriangle690.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 6 majorizationTriangle690
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray690
    majorizationLeaf690_polynomial_eq majorizationLeaf690_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 691. -/
def majorizationTriangle691 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 691. -/
def majorizationArray691 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (606747592204466366119352892973842749893295301 /
    3961408125713216879677197516800000000000000000 : ℚ) else
  if p = (0, 1) then (79017785901164783818476319945450094298691568089 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (3999581610999283 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-19319921447854889 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (79850904868243816430649068635163027822387429849 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (4995863851301487 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2532789116416283 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1194783465169877 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (4262467604009987 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-2269903123405579 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-9798556091123349 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (720058544844619 /
    24000000000000000 : ℚ) else
  if p = (3, 0) then (-9353076033911983 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-827435528649337 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (4551761680845019 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-28897157387186039 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf691_polynomial_eq :
    lowerPullbackPolynomial 17 6 majorizationTriangle691 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray691 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 6 majorizationTriangle691
    cellMatrix_17_6 cellMatrix_17_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf691_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray691 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf691_kernel {p : ℝ × ℝ} (hp : majorizationTriangle691.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 6 majorizationTriangle691
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray691
    majorizationLeaf691_polynomial_eq majorizationLeaf691_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 692. -/
def majorizationTriangle692 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 692. -/
def majorizationArray692 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (707557245558637483679525028657649282716124868507 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-29784636537747635435851318610833282847658661363 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-6788244066240971 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (19428811471108423 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-90734720872396656499650986498340548845617054169 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-239762690561669 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (784570915056581 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-1506116044714817 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1183749851158801 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (3924774180704253 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (8408490632256727 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3670776426108517 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (9353076033911983 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-827435528649337 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-4551761680845019 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (10638921568508273 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf692_polynomial_eq :
    lowerPullbackPolynomial 17 7 majorizationTriangle692 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray692 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 7 majorizationTriangle692
    cellMatrix_17_7 cellMatrix_17_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf692_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray692 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf692_kernel {p : ℝ × ℝ} (hp : majorizationTriangle692.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 7 majorizationTriangle692
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray692
    majorizationLeaf692_polynomial_eq majorizationLeaf692_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 693. -/
def majorizationTriangle693 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 693. -/
def majorizationArray693 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6247034268060181994449540926586602878835806921 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (25032958644715903028328448223910462903101494087 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (2058604587284741 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (25032958644715903028328448223910462903101494087 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (752865296771777 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (752865296771777 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-65594954169533 /
    6250000000000000 : ℚ) else
  if p = (2, 0) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (752865296771777 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (752865296771777 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-6781441287491117 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (1792567313737493 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-6152199798534007 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-13709717982144743 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (10638921568508273 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf693_polynomial_eq :
    lowerPullbackPolynomial 17 7 majorizationTriangle693 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray693 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 7 majorizationTriangle693
    cellMatrix_17_7 cellMatrix_17_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf693_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray693 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf693_kernel {p : ℝ × ℝ} (hp : majorizationTriangle693.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 7 majorizationTriangle693
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray693
    majorizationLeaf693_polynomial_eq majorizationLeaf693_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 694. -/
def majorizationTriangle694 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 694. -/
def majorizationArray694 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (216087872130476596876228796149815846394848063881 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-12684374671775465431176162049713682327763617389 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (3160141851216863 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-738484026088507 /
    150000000000000000 : ℚ) else
  if p = (1, 0) then (-38098862775641941014312142093580137571205583687 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (642597456630331 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (302092316321011 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-387218601398341 /
    37500000000000000 : ℚ) else
  if p = (2, 0) then (254543261050927 /
    12000000000000000 : ℚ) else
  if p = (2, 1) then (1193936657337561 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-4972695749142929 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (2287358431681871 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-1792567313737493 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-6152199798534007 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (13709717982144743 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-17488477073950111 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf694_polynomial_eq :
    lowerPullbackPolynomial 17 8 majorizationTriangle694 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray694 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 8 majorizationTriangle694
    cellMatrix_17_8 cellMatrix_17_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf694_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray694 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf694_kernel {p : ℝ × ℝ} (hp : majorizationTriangle694.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 8 majorizationTriangle694
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray694
    majorizationLeaf694_polynomial_eq majorizationLeaf694_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 695. -/
def majorizationTriangle695 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 695. -/
def majorizationArray695 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (752865296771777 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (2, 3) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (472344886475671 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (3, 2) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-17488477073950111 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf695_polynomial_eq :
    lowerPullbackPolynomial 17 8 majorizationTriangle695 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray695 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 8 majorizationTriangle695
    cellMatrix_17_8 cellMatrix_17_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf695_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray695 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf695_kernel {p : ℝ × ℝ} (hp : majorizationTriangle695.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 8 majorizationTriangle695
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray695
    majorizationLeaf695_polynomial_eq majorizationLeaf695_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 696. -/
def majorizationTriangle696 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 696. -/
def majorizationArray696 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (244739661886944820329955879005772603996303264177 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-46575018590705835778168267871803852714901912299 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-472344886475671 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-46575018590705835778168267871803852714901912299 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (472344886475671 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-472344886475671 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (2, 0) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (-472344886475671 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (472344886475671 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-472344886475671 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-472344886475671 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (472344886475671 /
    75000000000000000 : ℚ) else
  if p = (3, 2) then (-472344886475671 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (472344886475671 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf696_polynomial_eq :
    lowerPullbackPolynomial 17 9 majorizationTriangle696 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray696 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 9 majorizationTriangle696
    cellMatrix_17_9 cellMatrix_17_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf696_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray696 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf696_kernel {p : ℝ × ℝ} (hp : majorizationTriangle696.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 9 majorizationTriangle696
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray696
    majorizationLeaf696_polynomial_eq majorizationLeaf696_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 697. -/
def majorizationTriangle697 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 697. -/
def majorizationArray697 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (472344886475671 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf697_polynomial_eq :
    lowerPullbackPolynomial 17 9 majorizationTriangle697 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray697 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 9 majorizationTriangle697
    cellMatrix_17_9 cellMatrix_17_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf697_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray697 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf697_kernel {p : ℝ × ℝ} (hp : majorizationTriangle697.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 9 majorizationTriangle697
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray697
    majorizationLeaf697_polynomial_eq majorizationLeaf697_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 698. -/
def majorizationTriangle698 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 698. -/
def majorizationArray698 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf698_polynomial_eq :
    lowerPullbackPolynomial 17 10 majorizationTriangle698 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray698 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 10 majorizationTriangle698
    cellMatrix_17_10 cellMatrix_17_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf698_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray698 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf698_kernel {p : ℝ × ℝ} (hp : majorizationTriangle698.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 10 majorizationTriangle698
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray698
    majorizationLeaf698_polynomial_eq majorizationLeaf698_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 699. -/
def majorizationTriangle699 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 699. -/
def majorizationArray699 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (711022060156472424112090803227215618903815154063 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-11511599014797 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (118429596645487 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (-95218366573964161503286710876443250768409604903 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 2) then (-8159460874501 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (-33331258362557 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-26641115175133 /
    20000000000000000 : ℚ) else
  if p = (2, 2) then (-260459133309 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-3739515644173 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (9684577330897 /
    112500000000000000 : ℚ) else
  if p = (3, 2) then (-17684247417917 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (44459472272677 /
    600000000000000000 : ℚ) else
  if p = (0, 1) then (-29309718612033808421629799942950893218345193741 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf699_polynomial_eq :
    lowerPullbackPolynomial 18 0 majorizationTriangle699 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray699 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 0 majorizationTriangle699
    cellMatrix_18_0 cellMatrix_18_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf699_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray699 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf699_kernel {p : ℝ × ℝ} (hp : majorizationTriangle699.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 0 majorizationTriangle699
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray699
    majorizationLeaf699_polynomial_eq majorizationLeaf699_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 700. -/
def majorizationTriangle700 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 700. -/
def majorizationArray700 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (39829913043877663835116569372818017321333899547 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (3302792820043355501068255508482531639791963659 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-68792287030849 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-63472175552897 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (11105108680026212666652906736432075095066765857 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-299863220113679 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (29297957032753 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (6883649786149 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-754591650109849 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (1562140968477 /
    8000000000000000 : ℚ) else
  if p = (2, 2) then (32204383726361 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-103462291664647 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-76120685097379 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1619112505061 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-62641427146363 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (44459472272677 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf700_polynomial_eq :
    lowerPullbackPolynomial 18 0 majorizationTriangle700 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray700 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 0 majorizationTriangle700
    cellMatrix_18_0 cellMatrix_18_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf700_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray700 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf700_kernel {p : ℝ × ℝ} (hp : majorizationTriangle700.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 0 majorizationTriangle700
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray700
    majorizationLeaf700_polynomial_eq majorizationLeaf700_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
