/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelSourceInteriorFormula
public import PartialBalayage.Maximal.Square.FirstGeneratorLeaf

/-!
# The certificate's interior expression is the actual source density

The original physical generator, its sixteen-fold spatial scale, and the named actual
interior density agree exactly. The original sign symmetry retains both absolute spatial
coordinates, so the genuine rectangle positivity can apply to the full source density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The named literal interior expression has the actual original generator normalization. -/
theorem kernelGeneratorAt_scaled_eq_generatorInteriorDensity {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hr : u + v < 28) :
    kernelGeneratorAt (6 / 5) (u / 16) (v / 16) =
      stableNormalization (6 / 5) * generatorInteriorDensity u v :=
  kernelGeneratorAt_scaled_eq_interior hu hv hr

/-- The actual punctured source equals the certificate's full density on its exact spatial scale. -/
theorem squareGeneratorDensity_eq_generatorInteriorDensity {x : E} (hx₀ : x 0 ≠ 0)
    (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) < supportRadius) :
    squareGeneratorDensity x = stableNormalization (6 / 5) *
      generatorInteriorDensity (16 * |x 0|) (16 * |x 1|) := by
  have hu : 0 < |x 0| := abs_pos.mpr hx₀
  have hv : 0 < |x 1| := abs_pos.mpr hx₁
  have hrscaled : 16 * |x 0| + 16 * |x 1| < 28 := by
    norm_num only [supportRadius, diamondRadius] at hr
    linarith
  have he := kernelGeneratorAt_scaled_eq_generatorInteriorDensity
    (mul_pos (by norm_num) hu) (mul_pos (by norm_num) hv) hrscaled
  rw [show 16 * |x 0| / 16 = |x 0| by ring,
    show 16 * |x 1| / 16 = |x 1| by ring] at he
  rw [squareGeneratorDensity_eq_kernelGeneratorAt_abs hx₀ hx₁ (ne_of_lt hr)]
  exact he

end PartialBalayage.Maximal.Square
