/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialMass
public import PartialBalayage.Maximal.Square.SplineMass
public import PartialBalayage.Maximal.Square.MassCoefficientBound

/-!
# Exact mass and strict numerical bound for the actual square kernel

These conclusions concern the original integrable kernel with all 1,201
signed tensor coefficients. The separate generator and majorization proofs
are still needed to turn its mass into the square maximal-operator bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PartialBalayage.Maximal.Square

/-- The exact Lebesgue mass of the actual article kernel. -/
theorem integral_euclideanKernel :
    (∫ x, euclideanKernel x) = 3 * radialCoefficient * supportRadius ^ (4 / 5 : ℝ) +
      (coefficientSum : ℝ) / 256 := by
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin 2), radialBase (x 0) (x 1) +
        splineCorrection (x 0) (x 1) := integral_congr_ae euclideanKernel_ae_eq
    _ = _ := by rw [integral_add integrable_radialBase integrable_splineCorrection,
      integral_radialBase, integral_splineCorrection]

/-- Half the actual kernel mass is strictly less than the table's exact rational bound. -/
theorem half_integral_euclideanKernel_lt :
    (∫ x, euclideanKernel x) / 2 < 452 / 125 := by
  rw [integral_euclideanKernel]
  exact half_mass_coefficient_lt

end PartialBalayage.Maximal.Square
