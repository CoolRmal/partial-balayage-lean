/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.TableDefinitions
public import PartialBalayage.Maximal.SemigroupMajorantMass
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact one-dimensional semigroup table formulas

The squared-radius substitution evaluates the Poisson tail by the genuine arctangent integral
and the heat tail by its ordinary Gaussian integral. The Poisson tangency parameter is exactly
one fifth. The heat expression retains the actual transcendental tangency parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open PartialBalayage.Constants

namespace PartialBalayage

/-- The actual squared-radius Jacobian converts a half-power tail into an ordinary radial tail. -/
theorem integral_Ioi_half_weight (f : ℝ → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    (∫ z in Ioi b, z ^ (-(1 / 2 : ℝ)) * f z) =
      2 * ∫ r in Ioi (sqrt b), f (r ^ 2) := by
  have h := integral_comp_rpow_Ioi_of_pos'
    (g := fun z ↦ z ^ (-(1 / 2 : ℝ)) * f z) (p := 2) (by norm_num) hb
  have heq : (∫ r in Ioi (sqrt b),
      (2 * r ^ (2 - 1 : ℝ)) • ((r ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) * f (r ^ (2 : ℝ)))) =
      2 * ∫ r in Ioi (sqrt b), f (r ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hrpos : 0 < r := (sqrt_nonneg b).trans_lt hr
    simp only [show (2 - 1 : ℝ) = 1 by norm_num, rpow_one, rpow_two, smul_eq_mul]
    rw [rpow_neg (sq_nonneg r), ← sqrt_eq_rpow, sqrt_sq hrpos.le]
    field_simp
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← sqrt_eq_rpow, heq] at h
  exact h.symm

/-- The one-dimensional Poisson tail is the exact ordinary arctangent tail. -/
theorem poissonTail_one {b : ℝ} (hb : 0 ≤ b) :
    (∫ z in Ioi b, z ^ (-(1 / 2 : ℝ)) / (1 + z)) =
      Real.pi - 2 * arctan (sqrt b) := by
  have h := integral_Ioi_half_weight (fun z ↦ (1 + z)⁻¹) hb
  change (∫ z in Ioi b, z ^ (-(1 / 2 : ℝ)) * (1 + z)⁻¹) = _
  rw [h, integral_Ioi_inv_one_add_sq]
  ring

/-- The exact one-dimensional Poisson Gamma normalization is one over pi. -/
theorem poisson_one_gamma_factor :
    Gamma 1 / (sqrt Real.pi * Gamma (1 / 2)) = 1 / Real.pi := by
  rw [Gamma_one, Gamma_one_half_eq, mul_self_sqrt pi_nonneg]

/-- The one-dimensional Poisson mass has an exact elementary arctangent expression. -/
theorem poissonBoundFormula_one (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    poissonBoundFormula 1 a b =
      (2 * sqrt b / (1 + a) + Real.pi - 2 * arctan (sqrt b)) / Real.pi := by
  unfold poissonBoundFormula
  norm_num only [Nat.cast_one, show ((1 : ℝ) + 1) / 2 = 1 by norm_num,
    show (1 : ℝ) / 2 - 1 = -(1 / 2 : ℝ) by norm_num, mul_one, one_mul, rpow_one]
  rw [poisson_one_gamma_factor, ← sqrt_eq_rpow, poissonTail_one hb]
  ring

/-- The article's one-dimensional Poisson root is exactly one fifth. -/
theorem isPoissonTangencyParameter_one_fifth : IsPoissonTangencyParameter 1 (1 / 5) := by
  norm_num [IsPoissonTangencyParameter, rho_one, Real.rpow_two, Real.rpow_one]

/-- The selected Poisson mass is exactly the one-dimensional table constant. -/
theorem poissonBoundFormula_one_fifth :
    poissonBoundFormula 1 (1 / 5) (4 / 5) = poissonOneBound := by
  rw [poissonBoundFormula_one (1 / 5) (by norm_num)]
  have hsqrt : sqrt (4 / 5 : ℝ) = 2 / sqrt 5 := by
    rw [sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hsqrt, poissonOneBound]
  have hfive := sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hnonzero := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  field_simp [pi_ne_zero, hnonzero]
  nlinarith

/-- The one-dimensional heat tail is exactly the Gaussian tail after `z = r²`. -/
theorem heatTail_one {b : ℝ} (hb : 0 ≤ b) :
    (∫ z in Ioi b, z ^ (-(1 / 2 : ℝ)) * exp (-z)) =
      2 * ∫ r in Ioi (sqrt b), exp (-(r ^ 2)) :=
  integral_Ioi_half_weight (fun z ↦ exp (-z)) hb

/-- The one-dimensional heat mass has the exact complementary-error-function expression. -/
theorem heatBoundFormula_one (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    heatBoundFormula 1 a b = 2 * sqrt b / sqrt Real.pi * exp (-a) +
      complementaryErrorFunction (sqrt b) := by
  unfold heatBoundFormula complementaryErrorFunction
  norm_num only [Nat.cast_one, show (1 : ℝ) / 2 - 1 = -(1 / 2 : ℝ) by norm_num,
    div_one, Gamma_one_half_eq]
  rw [← sqrt_eq_rpow, heatTail_one hb]
  ring

/-- At the actual joining radius, the one-dimensional heat formula matches the article exactly. -/
theorem heatBoundFormula_one_join {a : ℝ} (ha : 0 ≤ a) :
    heatBoundFormula 1 a (rho 1 * a) = 4 * sqrt (a / Real.pi) * exp (-a) +
      complementaryErrorFunction (2 * sqrt a) := by
  rw [rho_one, heatBoundFormula_one a (mul_nonneg (by norm_num) ha),
    sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), sqrt_div ha]
  norm_num
  ring

/-- The genuine heat tangency equation in dimension one is exactly the article's root equation. -/
theorem isHeatTangencyParameter_one_iff (a : ℝ) :
    IsHeatTangencyParameter 1 a ↔ a ∈ Ioo (1 / 8) (1 / 2) ∧
      exp (-3 * a) = 1 - 2 * a := by
  norm_num [IsHeatTangencyParameter, rho_one]

end PartialBalayage
