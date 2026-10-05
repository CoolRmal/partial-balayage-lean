/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices34

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

/-- The actual closed rational triangle of majorization leaf 790. -/
def majorizationTriangle790 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 790. -/
def majorizationArray790 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (194269529736500489318438130213521070933892641161 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 2) then (-1943625556391327 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-28210147198462673121597232464016263873143575367 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 2) then (1943625556391327 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (1943625556391327 /
    150000000000000000 : ℚ) else
  if p = (2, 2) then (-1943625556391327 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-1943625556391327 /
    450000000000000000 : ℚ) else
  if p = (3, 2) then (1943625556391327 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (0, 1) then (-7350183980172231037353169715742579154126046829 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf790_polynomial_eq :
    lowerPullbackPolynomial 25 0 majorizationTriangle790 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray790 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 25 0 majorizationTriangle790
    cellMatrix_25_0 cellMatrix_25_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf790_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray790 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf790_kernel {p : ℝ × ℝ} (hp : majorizationTriangle790.Contains p) :
    (0 : ℝ) ≤ kernel (((25 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 25 0 majorizationTriangle790
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray790
    majorizationLeaf790_polynomial_eq majorizationLeaf790_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 791. -/
def majorizationTriangle791 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 791. -/
def majorizationArray791 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 0) then (1943625556391327 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf791_polynomial_eq :
    lowerPullbackPolynomial 25 0 majorizationTriangle791 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray791 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 25 0 majorizationTriangle791
    cellMatrix_25_0 cellMatrix_25_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf791_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray791 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf791_kernel {p : ℝ × ℝ} (hp : majorizationTriangle791.Contains p) :
    (0 : ℝ) ≤ kernel (((25 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 25 0 majorizationTriangle791
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray791
    majorizationLeaf791_polynomial_eq majorizationLeaf791_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 792. -/
def majorizationTriangle792 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 792. -/
def majorizationArray792 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (241831776727361618141795034538581871026281908657 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-43667133431122633590007423404613119744880556779 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1943625556391327 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-43667133431122633590007423404613119744880556779 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-1943625556391327 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (1943625556391327 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf792_polynomial_eq :
    lowerPullbackPolynomial 25 1 majorizationTriangle792 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray792 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 25 1 majorizationTriangle792
    cellMatrix_25_1 cellMatrix_25_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf792_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray792 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf792_kernel {p : ℝ × ℝ} (hp : majorizationTriangle792.Contains p) :
    (0 : ℝ) ≤ kernel (((25 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 25 1 majorizationTriangle792
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray792
    majorizationLeaf792_polynomial_eq majorizationLeaf792_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 793. -/
def majorizationTriangle793 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 793. -/
def majorizationArray793 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (1943625556391327 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf793_polynomial_eq :
    lowerPullbackPolynomial 25 1 majorizationTriangle793 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray793 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 25 1 majorizationTriangle793
    cellMatrix_25_1 cellMatrix_25_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf793_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray793 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf793_kernel {p : ℝ × ℝ} (hp : majorizationTriangle793.Contains p) :
    (0 : ℝ) ≤ kernel (((25 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 25 1 majorizationTriangle793
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray793
    majorizationLeaf793_polynomial_eq majorizationLeaf793_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 794. -/
def majorizationTriangle794 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 794. -/
def majorizationArray794 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf794_polynomial_eq :
    lowerPullbackPolynomial 25 2 majorizationTriangle794 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray794 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 25 2 majorizationTriangle794
    cellMatrix_25_2 cellMatrix_25_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf794_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray794 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf794_kernel {p : ℝ × ℝ} (hp : majorizationTriangle794.Contains p) :
    (0 : ℝ) ≤ kernel (((25 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 25 2 majorizationTriangle794
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray794
    majorizationLeaf794_polynomial_eq majorizationLeaf794_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 795. -/
def majorizationTriangle795 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 795. -/
def majorizationArray795 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (26527997677598736459669574764465289757877687913 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf795_polynomial_eq :
    lowerPullbackPolynomial 26 0 majorizationTriangle795 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray795 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 26 0 majorizationTriangle795
    cellMatrix_26_0 cellMatrix_26_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf795_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray795 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf795_kernel {p : ℝ × ℝ} (hp : majorizationTriangle795.Contains p) :
    (0 : ℝ) ≤ kernel (((26 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 26 0 majorizationTriangle795
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray795
    majorizationLeaf795_polynomial_eq majorizationLeaf795_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 796. -/
def majorizationTriangle796 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 796. -/
def majorizationArray796 (p : ℕ × ℕ) : ℚ :=
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf796_polynomial_eq :
    lowerPullbackPolynomial 26 0 majorizationTriangle796 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray796 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 26 0 majorizationTriangle796
    cellMatrix_26_0 cellMatrix_26_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf796_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray796 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf796_kernel {p : ℝ × ℝ} (hp : majorizationTriangle796.Contains p) :
    (0 : ℝ) ≤ kernel (((26 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 26 0 majorizationTriangle796
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray796
    majorizationLeaf796_polynomial_eq majorizationLeaf796_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 797. -/
def majorizationTriangle797 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 797. -/
def majorizationArray797 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf797_polynomial_eq :
    lowerPullbackPolynomial 26 1 majorizationTriangle797 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray797 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 26 1 majorizationTriangle797
    cellMatrix_26_1 cellMatrix_26_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf797_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray797 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf797_kernel {p : ℝ × ℝ} (hp : majorizationTriangle797.Contains p) :
    (0 : ℝ) ≤ kernel (((26 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 26 1 majorizationTriangle797
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray797
    majorizationLeaf797_polynomial_eq majorizationLeaf797_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 798. -/
def majorizationTriangle798 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 798. -/
def majorizationArray798 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf798_polynomial_eq :
    lowerPullbackPolynomial 27 0 majorizationTriangle798 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray798 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 27 0 majorizationTriangle798
    cellMatrix_27_0 cellMatrix_27_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf798_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray798 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf798_kernel {p : ℝ × ℝ} (hp : majorizationTriangle798.Contains p) :
    (0 : ℝ) ≤ kernel (((27 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 27 0 majorizationTriangle798
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray798
    majorizationLeaf798_polynomial_eq majorizationLeaf798_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
