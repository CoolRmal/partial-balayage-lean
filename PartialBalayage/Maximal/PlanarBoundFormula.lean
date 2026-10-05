/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupDefinitions
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exact planar semigroup bound formulas

The heat mass expression in dimension two has an elementary exponential tail. Its balanced
parameter equation gives the expression displayed in the table. These are exact formula
identities, separate from the pending unconditional maximal estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set

namespace PartialBalayage

/-- The planar heat bound has an elementary exponential tail. -/
theorem heatBoundFormula_two (a b : ℝ) :
    heatBoundFormula 2 a b = b * exp (-a) + exp (-b) := by
  norm_num [heatBoundFormula, Real.Gamma_one, integral_exp_neg_Ioi, integral_exp_Iic]
  ring

/-- The planar tangency equation gives the table's exact elementary heat expression. -/
theorem heatBoundFormula_two_of_balanced {a : ℝ}
    (ha : exp (-(exp 1 - 1) * a) = 1 - a) :
    heatBoundFormula 2 a (exp 1 * a) = (1 + (exp 1 - 1) * a) * exp (-a) := by
  have he : exp (-(exp 1 * a)) = exp (-a) * (1 - a) := by
    rw [← ha, ← exp_add]
    congr 1
    ring
  rw [heatBoundFormula_two, he]
  ring

/-- Translation by one moves the lower endpoint of an improper power integral. -/
theorem integral_one_add_rpow_Ioi (b s : ℝ) :
    (∫ z in Ioi b, (1 + z) ^ s) = ∫ z in Ioi (b + 1), z ^ s := by
  let f : ℝ → ℝ := (Ioi (b + 1)).indicator (fun z => z ^ s)
  have he : (fun z => f (z + 1)) = (Ioi b).indicator (fun z => (1 + z) ^ s) := by
    funext z
    by_cases hz : b < z
    · have hz' : b + 1 < z + 1 := by linarith
      simp [f, hz, hz', add_comm]
    · have hz' : ¬b + 1 < z + 1 := by linarith
      simp [f, hz, hz']
  rw [← integral_indicator measurableSet_Ioi, ← he, integral_add_right_eq_self f 1]
  exact integral_indicator measurableSet_Ioi

/-- The dimension-two Poisson tail is elementary. -/
theorem poissonTail_two {b : ℝ} (hb : 0 ≤ b) :
    (∫ z in Ioi b, 1 / (1 + z) ^ (3 / 2 : ℝ)) =
      2 / (1 + b) ^ (1 / 2 : ℝ) := by
  have hb1 : 0 < b + 1 := by linarith
  have he : (∫ z in Ioi b, 1 / (1 + z) ^ (3 / 2 : ℝ)) =
      ∫ z in Ioi b, (1 + z) ^ (-(3 / 2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    change 1 / (1 + z) ^ (3 / 2 : ℝ) = (1 + z) ^ (-(3 / 2 : ℝ))
    rw [Real.rpow_neg (by linarith [mem_Ioi.mp hz] : 0 ≤ 1 + z), one_div]
  rw [he, integral_one_add_rpow_Ioi,
    integral_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hb1]
  norm_num
  rw [Real.rpow_neg hb1.le, add_comm b 1]
  ring

/-- The planar Poisson normalization has the exact factor one half. -/
theorem poisson_planar_gamma_factor :
    Real.Gamma (3 / 2) / (sqrt Real.pi * Real.Gamma 1) = 1 / 2 := by
  have hΓ : Real.Gamma (3 / 2) = (1 / 2 : ℝ) * sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
  rw [hΓ, Real.Gamma_one, mul_one]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']

/-- The exact planar Poisson expression displayed in the article. -/
theorem poissonBoundFormula_two (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    poissonBoundFormula 2 a b = b / (2 * (1 + a) ^ (3 / 2 : ℝ)) +
      1 / (1 + b) ^ (1 / 2 : ℝ) := by
  unfold poissonBoundFormula
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) / 2 = 1 by norm_num,
    show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num,
    sub_self, Real.rpow_one, Real.rpow_zero]
  rw [poisson_planar_gamma_factor, poissonTail_two hb]
  ring

end PartialBalayage
