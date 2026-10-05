/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelGeneratorSymmetries

/-!
# Exact original source formula on the certificate's spatial scale

The original generator at positive physical coordinates has the genuine radial-plus-spline
formula. Substitution of the actual sixteen-fold grid scale yields the exact certificate
expression, and the full generator's sign symmetry reduces arbitrary coordinates to it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual full generator has the exact intrinsic, incoming-tail, and spline formula. -/
theorem kernelGeneratorAt_eq_interior {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : u + v < supportRadius) :
    kernelGeneratorAt (6 / 5) u v = stableNormalization (6 / 5) *
      (radialCoefficient * (squareIntrinsicConstant * (u + v) ^ (-12 / 5 : ℝ) +
        radialIncomingTail (6 / 5) supportRadius (u + v) (u - v)) +
          splineGeneratorFactor * splineGeneratorCorrectionPower (16 * u) (16 * v)) := by
  let x : E := WithLp.toLp 2 ![u, v]
  have hx₀ : x 0 = u := rfl
  have hx₁ : x 1 = v := rfl
  have hrx : diamondRadius (x 0) (x 1) < supportRadius := by
    simpa only [hx₀, hx₁, diamondRadius, abs_of_pos hu, abs_of_pos hv] using hr
  have he := coordinateStableGenerator_euclideanKernel_eq_density
    (by rw [hx₀]; exact hu.ne') (by rw [hx₁]; exact hv.ne') (ne_of_lt hrx)
  rw [coordinateStableGenerator_euclideanKernel_eq_at, hx₀, hx₁,
    squareGeneratorDensity_eq_formula, radialGeneratorDensity_eq_interior x
      (by rw [hx₀]; exact hu.ne') (by rw [hx₁]; exact hv.ne') hrx] at he
  rw [he]
  simp only [diamondInteriorSourceModel, hx₀, hx₁, diamondRadius,
    abs_of_pos hu, abs_of_pos hv]
  ring

/-- The exact sixteen-fold spatial scale is the original generator, including normalization. -/
theorem kernelGeneratorAt_scaled_eq_interior {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : u + v < 28) :
    kernelGeneratorAt (6 / 5) (u / 16) (v / 16) = stableNormalization (6 / 5) *
      (radialCoefficient * (squareIntrinsicConstant * ((u + v) / 16) ^ (-12 / 5 : ℝ) +
        radialIncomingTail (6 / 5) supportRadius ((u + v) / 16) ((u - v) / 16)) +
          splineGeneratorFactor * splineGeneratorCorrectionPower u v) := by
  have hphysical : u / 16 + v / 16 < supportRadius := by
    norm_num only [supportRadius]
    linarith
  rw [kernelGeneratorAt_eq_interior (by positivity) (by positivity) hphysical]
  rw [show u / 16 + v / 16 = (u + v) / 16 by ring,
    show u / 16 - v / 16 = (u - v) / 16 by ring,
    show 16 * (u / 16) = u by ring, show 16 * (v / 16) = v by ring]

/-- The genuine source density at a nonexceptional point is the positive-coordinate generator. -/
theorem squareGeneratorDensity_eq_kernelGeneratorAt_abs {x : E} (hx₀ : x 0 ≠ 0)
    (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) ≠ supportRadius) :
    squareGeneratorDensity x = kernelGeneratorAt (6 / 5) |x 0| |x 1| := by
  rw [kernelGeneratorAt_abs, ← coordinateStableGenerator_euclideanKernel_eq_at,
    coordinateStableGenerator_euclideanKernel_eq_density hx₀ hx₁ hr]

end PartialBalayage.Maximal.Square
