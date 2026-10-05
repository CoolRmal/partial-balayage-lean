/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonSubordinationIntegral
public import PartialBalayage.Maximal.OneDimensionalBoundFormula

/-!
# Exact positive Gaussian subordination

The ordinary positive-half-line integral is evaluated exactly. This is the scalar Laplace
identity behind the isotropic Poisson multiplier, with the genuine Euclidean frequency norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Linear

/-- Scaling the reciprocal Gaussian preserves its actual exact mass. -/
theorem integral_exp_scaled_sq_add_reciprocal_sq {t b : ℝ} (ht : 0 < t) (hb : 0 ≤ b) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(t ^ 2 * x ^ 2 + b ^ 2 / x ^ 2))) =
      Real.sqrt Real.pi / (2 * t) * Real.exp (-(2 * t * b)) := by
  let g : ℝ → ℝ := fun y ↦ Real.exp (-(y ^ 2 + (t * b / y) ^ 2))
  have heq : (∫ x in Ioi (0 : ℝ), Real.exp (-(t ^ 2 * x ^ 2 + b ^ 2 / x ^ 2))) =
      ∫ x in Ioi (0 : ℝ), g (t * x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change Real.exp (-(t ^ 2 * x ^ 2 + b ^ 2 / x ^ 2)) =
      Real.exp (-((t * x) ^ 2 + (t * b / (t * x)) ^ 2))
    congr 1
    field_simp [ht.ne', hx.ne']
  rw [heq, integral_comp_mul_left_Ioi g 0 ht]
  simp only [mul_zero, smul_eq_mul]
  rw [integral_exp_sq_add_reciprocal_sq (mul_nonneg ht.le hb)]
  rw [show 2 * (t * b) = 2 * t * b by ring]
  field_simp [ht.ne']

/-- The true positive subordination integrand is integrable before any evaluation. -/
theorem integrableOn_poisson_subordination {t b : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ ↦ u ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(t ^ 2 * u + b ^ 2 / u))) (Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ ↦ u ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(t ^ 2 * u))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2 : ℝ)) (p := 1)
        (b := t ^ 2) (by norm_num) (by norm_num) (by positivity))
  apply hbase.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u + b ^ 2 / u))‖ ≤
    u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u))
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le _)
  apply Real.exp_le_exp.mpr
  have hdiv : 0 ≤ b ^ 2 / u := div_nonneg (sq_nonneg b) hu.le
  linarith

/-- The exact Laplace--Gaussian integral is the isotropic Poisson exponential. -/
theorem integral_poisson_subordination {t b : ℝ} (ht : 0 < t) (hb : 0 ≤ b) :
    (∫ u in Ioi (0 : ℝ), u ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(t ^ 2 * u + b ^ 2 / u))) =
      Real.sqrt Real.pi / t * Real.exp (-(2 * t * b)) := by
  rw [PartialBalayage.integral_Ioi_half_weight
    (fun u ↦ Real.exp (-(t ^ 2 * u + b ^ 2 / u))) (by norm_num : (0 : ℝ) ≤ 0)]
  simp only [Real.sqrt_zero]
  rw [integral_exp_scaled_sq_add_reciprocal_sq ht hb]
  ring

end PartialBalayage.Linear
