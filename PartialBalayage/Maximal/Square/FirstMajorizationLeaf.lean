/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RationalEvaluation
public import PartialBalayage.Maximal.Square.ArrayPolynomial
public import PartialBalayage.Maximal.Square.Data.CellMatrices0
public import PartialBalayage.Maximal.Square.SquareGridGeometry

/-!
# The first actual majorization leaf

The rational normal form is identified with the actual signed kernel lower polynomial.
All twenty-eight Bernstein inequalities are ordinary rational proofs. Together they give
an actual kernel inequality on the first closed grid triangle, including the origin.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The literal rational monomial array of the first lower polynomial. -/
def firstMajorizationArray (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4768076816976185873290508116697109047727186691489 /
    57044277010270323067351644241920000000000000000 : ℚ) else
  if p = (0, 2) then (4272954493350132607 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-12484546856254210157 /
    900000000000000000 : ℚ) else
  if p = (2, 0) then (4272954493350132607 /
    150000000000000000 : ℚ) else
  if p = (2, 2) then (-340992498652911263 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (549436948932703163 /
    15000000000000000 : ℚ) else
  if p = (3, 0) then (-12484546856254210157 /
    900000000000000000 : ℚ) else
  if p = (3, 2) then (549436948932703163 /
    15000000000000000 : ℚ) else
  if p = (3, 3) then (-18011598276544751507 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-1906643824431262624916613107470110939381491072661 /
    31691265005705735037417580134400000000000000000 : ℚ) else
  if p = (0, 1) then (-1906643824431262624916613107470110939381491072661 /
    31691265005705735037417580134400000000000000000 : ℚ) else
  0

/-- The actual first lower polynomial is the checked rational monomial array. -/
theorem firstMajorizationPolynomial_eq_array :
    lowerPullbackPolynomial 0 0 lowerCellTriangle radialPowerData0.radius
      (certifiedRadialHeight radialPowerData0 radialPowerData32)
      (certifiedRadialSlope radialPowerData0) 1 =
        planeArrayPolynomial firstMajorizationArray := by
  have hHeight : certifiedRadialHeight radialPowerData0 radialPowerData32 =
      (194966155051932688366838459208365618564210237813 /
        3961408125713216879677197516800000000000000000 : ℚ) := by
    norm_num [certifiedRadialHeight, radialCoefficientRat, supportRadiusRat,
      radialPowerData0, radialPowerData32]
  have hSlope : certifiedRadialSlope radialPowerData0 =
      (1906643824431262624916613107470110939381491072661 /
        1980704062856608439838598758400000000000000000 : ℚ) := by
    norm_num [certifiedRadialSlope, radialCoefficientRat, radialPowerData0]
  apply planePolynomial_eq_array_of_eval
  intro z
  rw [lowerPullbackPolynomial_eval_rat, hHeight, hSlope]
  simp only [correctionCellCoefficient_eq_matrix 0 0 cellMatrix_0_0
    cellMatrix_0_0_correct, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num (config := { maxSteps := 1000000 }) [lowerCellTriangle,
    RationalTriangle.rationalPoint, cellMatrixExtension, cellMatrix_0_0,
    radialPowerData0, triangleIndices, firstMajorizationArray, Finset.sum_filter,
    Finset.product_eq_sprod, Finset.sum_product, Finset.sum_range_succ]
  ring

/-- Every actual Bernstein coefficient of the first literal array is nonnegative. -/
theorem firstMajorizationArray_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient firstMajorizationArray p.1 p.2 := by
  rintro ⟨a, b⟩ hp
  have hab := mem_triangleIndices.mp hp
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 6 := by omega
  interval_cases a <;> interval_cases b <;> try omega
  all_goals norm_num (config := { maxSteps := 1000000 }) [triangleBernsteinCoefficient,
    triangleIndices, firstMajorizationArray, monomialBernsteinCoefficient, Nat.choose,
    Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_range_succ]

/-- The actual kernel majorizes one throughout the first closed quarter-grid triangle. -/
theorem one_le_kernel_firstTriangle {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 1) : 1 ≤ kernel (x / 16) (y / 16) := by
  have hR : radialPowerData32.radius = supportRadiusRat := by
    norm_num [radialPowerData32, supportRadiusRat]
  have hT : lowerCellTriangle.InUnitBox := by
    norm_num [RationalTriangle.InUnitBox, vertexInUnitBox, lowerCellTriangle]
  have hr : diamondRadius (((0 : ℝ) + (lowerCellTriangle.point x y).1) / 16)
      (((0 : ℝ) + (lowerCellTriangle.point x y).2) / 16) ≤
        (radialPowerData0.radius : ℝ) := by
    simp only [RationalTriangle.point, lowerCellTriangle, Rat.cast_zero, Rat.cast_one,
      sub_zero, sub_self, one_mul, zero_mul, add_zero, zero_add]
    have hx' : 0 ≤ x / 16 := div_nonneg hx (by norm_num)
    have hy' : 0 ≤ y / 16 := div_nonneg hy (by norm_num)
    rw [diamondRadius, abs_of_nonneg hx', abs_of_nonneg hy']
    norm_num [radialPowerData0]
    linarith
  have hc : ∀ p ∈ triangleIndices, 0 ≤ triangleBernsteinCoefficient
      (planePolynomialCoefficients (lowerPullbackPolynomial 0 0 lowerCellTriangle
        radialPowerData0.radius (certifiedRadialHeight radialPowerData0 radialPowerData32)
        (certifiedRadialSlope radialPowerData0) 1)) p.1 p.2 := by
    intro p hp
    rw [firstMajorizationPolynomial_eq_array, planeArrayPolynomial_bernsteinCoefficient]
    exact firstMajorizationArray_bernstein_nonneg p hp
  have h := kernel_ge_target_of_lowerPullback 0 0 lowerCellTriangle
    radialPowerData0 radialPowerData32 radialPowerData0_valid radialPowerData32_valid
    hR (1 : Fin 2) hT hx hy hxy (by simpa only [Nat.cast_zero] using hr) hc
  simpa [lowerCellTriangle, RationalTriangle.point] using h

end PartialBalayage.Maximal.Square
