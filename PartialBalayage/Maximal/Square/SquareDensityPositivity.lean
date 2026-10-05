/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorInteriorTransport
public import PartialBalayage.Maximal.Square.KernelGeneratorAlmostEverywhere

/-!
# Geometric positivity transport to the genuine source density

Actual coordinate swapping preserves the named interior expression. Positivity on the
ordered interior domain therefore gives source positivity on the entire plane outside
the already proved null axes and diamond boundary. The geometry premise is explicit.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The literal interior expression inherits swapping from the genuine original generator. -/
theorem generatorInteriorDensity_swap {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : u + v < 28) : generatorInteriorDensity u v = generatorInteriorDensity v u := by
  have he₁ := kernelGeneratorAt_scaled_eq_generatorInteriorDensity hu hv hr
  have he₂ := kernelGeneratorAt_scaled_eq_generatorInteriorDensity hv hu
    (by simpa only [add_comm] using hr)
  rw [kernelGeneratorAt_swap] at he₁
  exact mul_left_cancel₀ (stableNormalization_pos (by norm_num) (by norm_num)).ne'
    (he₁.symm.trans he₂)

/-- An actual ordered-interior proof covers the full positive-coordinate interior. -/
theorem generatorInteriorDensity_pos_of_ordered_interior
    (hinterior : ∀ {u v : ℝ}, 0 < v → v ≤ u → u + v < 28 →
      0 < generatorInteriorDensity u v) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hr : u + v < 28) :
    0 < generatorInteriorDensity u v := by
  by_cases hvu : v ≤ u
  · exact hinterior hv hvu hr
  · rw [generatorInteriorDensity_swap hu hv hr]
    exact hinterior hu (le_of_lt (lt_of_not_ge hvu)) (by simpa only [add_comm] using hr)

/-- Actual ordered-interior positivity gives almost-everywhere nonnegativity of the source. -/
theorem ae_squareGeneratorDensity_nonneg_of_ordered_interior
    (hinterior : ∀ {u v : ℝ}, 0 < v → v ≤ u → u + v < 28 →
      0 < generatorInteriorDensity u v) :
    ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x := by
  filter_upwards [ae_euclidean_coordinate_ne_zero 0, ae_euclidean_coordinate_ne_zero 1,
    ae_diamondRadius_ne supportRadius] with x hx₀ hx₁ hne
  by_cases hr : diamondRadius (x 0) (x 1) < supportRadius
  · rw [squareGeneratorDensity_eq_generatorInteriorDensity hx₀ hx₁ hr]
    have hrscaled : 16 * |x 0| + 16 * |x 1| < 28 := by
      norm_num only [supportRadius, diamondRadius] at hr
      linarith
    apply mul_nonneg (stableNormalization_pos (by norm_num) (by norm_num)).le
    exact (generatorInteriorDensity_pos_of_ordered_interior hinterior
      (mul_pos (by norm_num) (abs_pos.mpr hx₀))
      (mul_pos (by norm_num) (abs_pos.mpr hx₁)) hrscaled).le
  · exact squareGeneratorDensity_nonneg_exterior hx₀ hx₁
      (lt_of_le_of_ne (le_of_not_gt hr) hne.symm)

end PartialBalayage.Maximal.Square
