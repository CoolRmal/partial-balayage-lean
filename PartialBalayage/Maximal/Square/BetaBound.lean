/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.BetaIntegral

/-!
# Kernel-checked numerical upper bound for the actual beta integral

The sixty-term rational inequality and fifth-power inequality are checked by
Lean's kernel. The analytic series and integration proofs identify their
result with the original real integral.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- An exact rational fifth-power enclosure of the actual half's fifth root. -/
theorem half_fifth_root_enclosure :
    IsPowerEnclosure (1 / 2) 1 0 (870550563297 / 10 ^ 12) := by
  norm_num [IsPowerEnclosure]

/-- The true real half's fifth root is bounded by its exact rational enclosure. -/
theorem half_rpow_fifth_le :
    (1 / 2 : ℝ) ^ (1 / 5 : ℝ) ≤ 870550563297 / 10 ^ 12 := by
  simpa using (half_fifth_root_enclosure.rpow_bounds (by norm_num)).2

set_option maxRecDepth 2048 in
/-- The actual sixty-term rational sum satisfies the required numerical inequality. -/
theorem betaBinomialSum_sixty_bound :
    (870550563297 / 10 ^ 12 : ℚ) * betaBinomialSum 60 ≤ 678678670707 / 10 ^ 12 := by
  decide +kernel

/-- The original convergent beta integral satisfies its genuine rational upper bound. -/
theorem squareBetaIntegral_le : squareBetaIntegral ≤ 678678670707 / 10 ^ 12 := by
  have hb := squareBetaIntegral_le_binomialSum (N := 60) (by norm_num)
  have hc : 0 < (1 / 2 : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hs : 0 ≤ (betaBinomialSum 60 : ℝ) := by
    apply le_of_not_gt
    intro hn
    have hm := mul_neg_of_pos_of_neg hc hn
    linarith [squareBetaIntegral_pos]
  calc
    _ ≤ (1 / 2 : ℝ) ^ (1 / 5 : ℝ) * (betaBinomialSum 60 : ℝ) := hb
    _ ≤ (870550563297 / 10 ^ 12 : ℝ) * (betaBinomialSum 60 : ℝ) :=
      mul_le_mul_of_nonneg_right half_rpow_fifth_le hs
    _ ≤ _ := by
      have h : (((870550563297 / 10 ^ 12 : ℚ) * betaBinomialSum 60 : ℚ) : ℝ) ≤
          ((678678670707 / 10 ^ 12 : ℚ) : ℝ) := by
        exact_mod_cast betaBinomialSum_sixty_bound
      simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h

end PartialBalayage.Maximal.Square
