/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorInteriorPositivity
public import PartialBalayage.Maximal.Square.SquareDensityPositivity
public import PartialBalayage.Maximal.Square.SquareSourcePrerequisites

/-!
# The genuine nonnegative source of the exact square comparison kernel

The checked finite partition proves positivity of the actual interior generator.
Coordinate symmetry and the exterior jump formula give nonnegativity almost everywhere.
The fixed positive source measure then has the true punctured pairing, finite jump moment,
and full compensated identity, with no positivity or source certificate premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual generator density of the exact square kernel is nonnegative almost everywhere. -/
theorem ae_squareGeneratorDensity_nonneg :
    ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x :=
  ae_squareGeneratorDensity_nonneg_of_ordered_interior
    generatorInteriorDensity_pos_on_ordered_interior

/-- The fixed positive source measure gives the genuine punctured generator pairing. -/
theorem integral_kernel_generator_eq_squareSourceMeasure {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    (∫ x : E, euclideanKernel x * coordinateStableGenerator (6 / 5) φ x) =
      ∫ x, φ x ∂squareSourceMeasure :=
  integral_kernel_generator_eq_squareSourceMeasure_of_nonneg
    ae_squareGeneratorDensity_nonneg hφ hs hzero

/-- The true positive source has a finite truncated second moment. -/
theorem integrable_squareSourceMeasure_jumpMoment :
    Integrable compensatedJumpMoment squareSourceMeasure :=
  integrable_squareSourceMeasure_jumpMoment_of_nonneg ae_squareGeneratorDensity_nonneg

/-- The exact square kernel has the full compensated source identity for every compact C² test. -/
theorem integral_kernel_generator_eq_squareCompensatedSource {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x : E, euclideanKernel x * coordinateStableGenerator (6 / 5) φ x) =
      compensatedSymmetricSource squareSourceMeasure φ :=
  integral_kernel_generator_eq_squareCompensatedSource_of_nonneg
    ae_squareGeneratorDensity_nonneg hφ hs

end PartialBalayage.Maximal.Square
