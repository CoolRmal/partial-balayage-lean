/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.BetaBound
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A genuine lower bound for the square's intrinsic fractional constant

The exact half-angle identity, proved bounds for pi, and the actual beta
integral give the rational constant used by the generator arithmetic.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual intrinsic constant at order six fifths. -/
def squareIntrinsicConstant : ℝ :=
  2 * Real.pi * Real.tan (Real.pi / 10) / ((6 / 5 : ℝ) * squareBetaIntegral)

/-- The exact half-angle relation derived from the genuine cosine value. -/
theorem tan_pi_div_ten_sq_identity :
    Real.tan (Real.pi / 10) ^ 2 * (5 + Real.sqrt 5) = 3 - Real.sqrt 5 := by
  have hp : 0 < Real.pi / 10 := by positivity
  have hq : Real.pi / 10 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hc : Real.cos (Real.pi / 10) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hq⟩).ne'
  have hdouble := Real.cos_two_mul (Real.pi / 10)
  have hang : 2 * (Real.pi / 10) = Real.pi / 5 := by ring
  rw [hang, Real.cos_pi_div_five] at hdouble
  have hc₂ : 8 * Real.cos (Real.pi / 10) ^ 2 = 5 + Real.sqrt 5 := by linarith
  have hs₂ : 8 * Real.sin (Real.pi / 10) ^ 2 = 3 - Real.sqrt 5 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 10)]
  have ht : Real.tan (Real.pi / 10) ^ 2 * Real.cos (Real.pi / 10) ^ 2 =
      Real.sin (Real.pi / 10) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow]
    field_simp
  calc
    _ = Real.tan (Real.pi / 10) ^ 2 * (8 * Real.cos (Real.pi / 10) ^ 2) := by rw [hc₂]
    _ = 8 * (Real.tan (Real.pi / 10) ^ 2 * Real.cos (Real.pi / 10) ^ 2) := by ring
    _ = _ := by rw [ht, hs₂]

/-- A kernel-checked rational lower bound for the actual tangent at pi over ten. -/
theorem tan_pi_div_ten_ge : 324919696232 / 10 ^ 12 ≤ Real.tan (Real.pi / 10) := by
  have hs : Real.sqrt 5 ≤ (2236067977500 / 10 ^ 12 : ℝ) := by
    have hnum : (5 : ℝ) ≤ (2236067977500 / 10 ^ 12 : ℝ) ^ 2 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have ht : 0 ≤ Real.tan (Real.pi / 10) :=
    (Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity)
      (by linarith [Real.pi_pos])).le
  have hnum : (324919696232 / 10 ^ 12 : ℝ) ^ 2 * (5 + 2236067977500 / 10 ^ 12) ≤
      3 - 2236067977500 / 10 ^ 12 := by norm_num
  have hbound : (324919696232 / 10 ^ 12 : ℝ) ^ 2 * (5 + Real.sqrt 5) ≤
      3 - Real.sqrt 5 := by nlinarith
  have hd : 0 < 5 + Real.sqrt 5 := by positivity
  apply le_of_not_gt
  intro hlt
  have hsq : Real.tan (Real.pi / 10) ^ 2 < (324919696232 / 10 ^ 12 : ℝ) ^ 2 := by
    nlinarith
  have hm := mul_lt_mul_of_pos_right hsq hd
  rw [tan_pi_div_ten_sq_identity] at hm
  linarith

/-- The actual intrinsic constant exceeds the article's exact rational lower estimate. -/
theorem squareIntrinsicConstant_ge : 125337337 / 50000000 ≤ squareIntrinsicConstant := by
  have hd : 0 < (6 / 5 : ℝ) * squareBetaIntegral :=
    mul_pos (by norm_num) squareBetaIntegral_pos
  unfold squareIntrinsicConstant
  apply (le_div_iff₀ hd).mpr
  have ht : 0 ≤ Real.tan (Real.pi / 10) :=
    (by norm_num : (0 : ℝ) ≤ 324919696232 / 10 ^ 12).trans tan_pi_div_ten_ge
  have hp : (314159265358979323846 / 10 ^ 20 : ℝ) ≤ Real.pi := by
    convert Real.pi_gt_d20.le using 1
    norm_num
  have hprod := mul_le_mul hp tan_pi_div_ten_ge
    (by norm_num : (0 : ℝ) ≤ 324919696232 / 10 ^ 12) Real.pi_pos.le
  have hnum : (125337337 / 50000000 : ℝ) * ((6 / 5 : ℝ) * (678678670707 / 10 ^ 12)) ≤
      2 * (314159265358979323846 / 10 ^ 20) * (324919696232 / 10 ^ 12) := by norm_num
  nlinarith [squareBetaIntegral_le]

end PartialBalayage.Maximal.Square
