/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Kernel
public import PartialBalayage.Maximal.Square.PowerEnclosure

/-!
# Exact rational bound for the square mass coefficient

A rational fifth-power inequality encloses the true radius to the power four
fifths. Together with the actual signed coefficient sum it puts the exact
half-mass expression strictly below the table's rational value 3.616.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- A kernel-checked rational enclosure for the actual support-radius power. -/
theorem supportRadius_rpow_four_fifths_le :
    supportRadius ^ (4 / 5 : ℝ) ≤ 15647 / 10000 := by
  have he : IsPowerEnclosure (7 / 4) 4 0 (15647 / 10000) := by
    norm_num [IsPowerEnclosure]
  have hp := (he.rpow_bounds (by norm_num)).2
  simpa only [supportRadius, Rat.cast_div, Rat.cast_ofNat, Int.cast_ofNat] using hp

/-- The true half-mass formula is strictly less than the article's bound. -/
theorem half_mass_coefficient_lt :
    (3 * radialCoefficient * supportRadius ^ (4 / 5 : ℝ) +
      (coefficientSum : ℝ) / 256) / 2 < 452 / 125 := by
  calc
    _ ≤ (3 * radialCoefficient * (15647 / 10000) + (coefficientSum : ℝ) / 256) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add (mul_le_mul_of_nonneg_left supportRadius_rpow_four_fifths_le
        (mul_nonneg (by norm_num) radialCoefficient_pos.le)) le_rfl
    _ < _ := by rw [coefficientSum_eq]; norm_num [radialCoefficient]

end PartialBalayage.Maximal.Square
