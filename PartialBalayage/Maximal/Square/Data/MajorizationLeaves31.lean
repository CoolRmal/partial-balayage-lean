/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices31

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

/-- The actual closed rational triangle of majorization leaf 758. -/
def majorizationTriangle758 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 758. -/
def majorizationArray758 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (209468157584629011031025902966871458195356234121 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-33742266091547513966494959943498608382482649927 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (8656593130345759 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-5606380728504649 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-34733641852232598561084628064482552318255240007 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (3807460454644667 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2292964349037553 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-5343176750878663 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (10533531322317451 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (1667318285046989 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-7767743088729209 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (10817955490570319 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-7796141952471623 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-4404707654892817 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (10505132458575037 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-13555344860416147 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf758_polynomial_eq :
    lowerPullbackPolynomial 21 4 majorizationTriangle758 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray758 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 4 majorizationTriangle758
    cellMatrix_21_4 cellMatrix_21_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf758_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray758 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf758_kernel {p : ℝ × ℝ} (hp : majorizationTriangle758.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 4 majorizationTriangle758
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray758
    majorizationLeaf758_polynomial_eq majorizationLeaf758_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 759. -/
def majorizationTriangle759 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 759. -/
def majorizationArray759 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (684347342461457 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (2, 3) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (101673746728037 /
    60000000000000000 : ℚ) else
  if p = (3, 1) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (3, 2) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (3, 3) then (-13555344860416147 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf759_polynomial_eq :
    lowerPullbackPolynomial 21 4 majorizationTriangle759 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray759 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 4 majorizationTriangle759
    cellMatrix_21_4 cellMatrix_21_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf759_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray759 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf759_kernel {p : ℝ × ℝ} (hp : majorizationTriangle759.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 4 majorizationTriangle759
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray759
    majorizationLeaf759_polynomial_eq majorizationLeaf759_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 760. -/
def majorizationTriangle760 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 760. -/
def majorizationArray760 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (81195077858636822856957065172373876398987150139 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-15140196759890494673027861461050959305186699513 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (-101673746728037 /
    60000000000000000 : ℚ) else
  if p = (1, 0) then (-15140196759890494673027861461050959305186699513 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (305021240184111 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (-305021240184111 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (2, 0) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (-305021240184111 /
    20000000000000000 : ℚ) else
  if p = (2, 2) then (305021240184111 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (-101673746728037 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (-101673746728037 /
    60000000000000000 : ℚ) else
  if p = (3, 1) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (3, 2) then (-101673746728037 /
    20000000000000000 : ℚ) else
  if p = (3, 3) then (101673746728037 /
    60000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf760_polynomial_eq :
    lowerPullbackPolynomial 21 5 majorizationTriangle760 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray760 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 5 majorizationTriangle760
    cellMatrix_21_5 cellMatrix_21_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf760_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray760 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf760_kernel {p : ℝ × ℝ} (hp : majorizationTriangle760.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 5 majorizationTriangle760
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray760
    majorizationLeaf760_polynomial_eq majorizationLeaf760_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 761. -/
def majorizationTriangle761 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 761. -/
def majorizationArray761 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (101673746728037 /
    60000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf761_polynomial_eq :
    lowerPullbackPolynomial 21 5 majorizationTriangle761 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray761 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 5 majorizationTriangle761
    cellMatrix_21_5 cellMatrix_21_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf761_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray761 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf761_kernel {p : ℝ × ℝ} (hp : majorizationTriangle761.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 5 majorizationTriangle761
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray761
    majorizationLeaf761_polynomial_eq majorizationLeaf761_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 762. -/
def majorizationTriangle762 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 762. -/
def majorizationArray762 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf762_polynomial_eq :
    lowerPullbackPolynomial 21 6 majorizationTriangle762 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray762 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 6 majorizationTriangle762
    cellMatrix_21_6 cellMatrix_21_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf762_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray762 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf762_kernel {p : ℝ × ℝ} (hp : majorizationTriangle762.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 6 majorizationTriangle762
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray762
    majorizationLeaf762_polynomial_eq majorizationLeaf762_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 763. -/
def majorizationTriangle763 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 763. -/
def majorizationArray763 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1047774287284337789746948273189403833115421717623 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 2) then (-729094242524039 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-1069868166119 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (-73715305858481914909768589212351507064189706461 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 2) then (44306293896371 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-1006576656610901 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-572085568406557 /
    300000000000000000 : ℚ) else
  if p = (2, 2) then (151350521208767 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-27884258457031 /
    4687500000000000 : ℚ) else
  if p = (3, 0) then (70303869253957 /
    90000000000000000 : ℚ) else
  if p = (3, 2) then (-1449555276103507 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (199851653897073 /
    25000000000000000 : ℚ) else
  if p = (0, 1) then (-19251666595781250300207259216300106940023862687 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf763_polynomial_eq :
    lowerPullbackPolynomial 22 0 majorizationTriangle763 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray763 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 0 majorizationTriangle763
    cellMatrix_22_0 cellMatrix_22_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf763_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray763 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf763_kernel {p : ℝ × ℝ} (hp : majorizationTriangle763.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 0 majorizationTriangle763
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray763
    majorizationLeaf763_polynomial_eq majorizationLeaf763_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 764. -/
def majorizationTriangle764 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 764. -/
def majorizationArray764 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (15817170916164660134004145298141273401458814499 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (17691697303961912256710335847482352621672495203 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-864863103372571 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (592098697059311 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (19215091019260279089363840363595375283644954723 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-580489788304513 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-1019204006439623 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (2618897801183759 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-1340105278938181 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-51415629018797 /
    6250000000000000 : ℚ) else
  if p = (2, 2) then (1558179265836349 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-1352516749761161 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (199908355946711 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (6982192179403 /
    1500000000000000 : ℚ) else
  if p = (3, 2) then (-2147774494043807 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (199851653897073 /
    25000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf764_polynomial_eq :
    lowerPullbackPolynomial 22 0 majorizationTriangle764 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray764 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 0 majorizationTriangle764
    cellMatrix_22_0 cellMatrix_22_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf764_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray764 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf764_kernel {p : ℝ × ℝ} (hp : majorizationTriangle764.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 0 majorizationTriangle764
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray764
    majorizationLeaf764_polynomial_eq majorizationLeaf764_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 765. -/
def majorizationTriangle765 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 765. -/
def majorizationArray765 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (213265294723165523062191930561431817719039440519 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-5154341349726506564580988145911704402922580001 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (-1463537825878673 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-3131322168636773 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-17725144311257741001743567823609254439943174243 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-829351481025417 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-917964068818159 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (4212823008266809 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-540471855151337 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-71723546447481 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (-294797614103729 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (1677764347648799 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-199908355946711 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (6982192179403 /
    1500000000000000 : ℚ) else
  if p = (3, 2) then (2147774494043807 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-10507034028332999 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf765_polynomial_eq :
    lowerPullbackPolynomial 22 1 majorizationTriangle765 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray765 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 1 majorizationTriangle765
    cellMatrix_22_1 cellMatrix_22_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf765_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray765 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf765_kernel {p : ℝ × ℝ} (hp : majorizationTriangle765.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 1 majorizationTriangle765
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray765
    majorizationLeaf765_polynomial_eq majorizationLeaf765_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 766. -/
def majorizationTriangle766 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 766. -/
def majorizationArray766 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5200801712322971905399231776816834562075173613 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (22177291817486014017325580095777742163538269683 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (6740639187249073 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-4553181338076547 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (22736450917012202652445380627874023665740207603 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (2892234877238267 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2014806440968047 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-23601571911199 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (1665718939908467 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-1485487936870293 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-6392529255076607 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (4208415439474001 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-5769294819784799 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-519497616277171 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (1242297008049077 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (-10507034028332999 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf766_polynomial_eq :
    lowerPullbackPolynomial 22 1 majorizationTriangle766 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray766 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 1 majorizationTriangle766
    cellMatrix_22_1 cellMatrix_22_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf766_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray766 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf766_kernel {p : ℝ × ℝ} (hp : majorizationTriangle766.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 1 majorizationTriangle766
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray766
    majorizationLeaf766_polynomial_eq majorizationLeaf766_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 767. -/
def majorizationTriangle767 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 767. -/
def majorizationArray767 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (214000041799403293168480095771800745757764844169 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-71572760302205894543772612766236246526487986649 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-2019465940131373 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (2294111734624639 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-76320097822883297569159259184396859769449906649 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1117736229056661 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2376894870630491 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-134542410785789 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-1069998313342421 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (504896633884927 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (6030440825414163 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-434843073089313 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (5769294819784799 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-519497616277171 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-1242297008049077 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (3648557017809859 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf767_polynomial_eq :
    lowerPullbackPolynomial 22 2 majorizationTriangle767 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray767 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 2 majorizationTriangle767
    cellMatrix_22_2 cellMatrix_22_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf767_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray767 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf767_kernel {p : ℝ × ℝ} (hp : majorizationTriangle767.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 2 majorizationTriangle767
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray767
    majorizationLeaf767_polynomial_eq majorizationLeaf767_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 768. -/
def majorizationTriangle768 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 768. -/
def majorizationArray768 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6195107899605986435652691169475958209154044617 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (23994431275631991852391453081697569509466248007 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (119086625781831 /
    50000000000000000 : ℚ) else
  if p = (1, 0) then (23994431275631991852391453081697569509466248007 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1117081775017801 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-737170826181647 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (869495524088323 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-166399720278197 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (-73971656456003 /
    4687500000000000 : ℚ) else
  if p = (3, 3) then (3648557017809859 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf768_polynomial_eq :
    lowerPullbackPolynomial 22 2 majorizationTriangle768 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray768 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 2 majorizationTriangle768
    cellMatrix_22_2 cellMatrix_22_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf768_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray768 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf768_kernel {p : ℝ × ℝ} (hp : majorizationTriangle768.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 2 majorizationTriangle768
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray768
    majorizationLeaf768_polynomial_eq majorizationLeaf768_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
