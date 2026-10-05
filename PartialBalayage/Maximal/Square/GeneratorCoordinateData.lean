/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorCubicIntervalData
public import PartialBalayage.Maximal.Square.GeneratorPowerCache
public import PartialBalayage.Maximal.Square.GeneratorFiniteKnots

/-!
# Genuine coordinate data with shared signed power bounds

The cubic rows and interval bounds are checked against the actual spline
coefficient matrix. The signed Taylor centers reference proved root bounds, and
the remaining metadata equalities identify their true coordinate midpoints.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- One actual coordinate interval with indices into proved positive-center root data. -/
structure GeneratorCoordinateData where
  cubic : GeneratorCubicIntervalData
  roots : Fin 53 → Fin 47 × Fin 64
  negative : Fin 53 → Bool

namespace GeneratorCoordinateData

/-- The actual signed Taylor family selected from the shared root bounds. -/
def powers (D : GeneratorCoordinateData) : Fin 53 → GeneratorPowerTaylorData :=
  GeneratorPowerTaylorData.signedFamily
    (fun k ↦ generatorPowerCache (D.roots k).1 (D.roots k).2) D.negative

/-- Checks that the selected data refer to the actual coordinate interval. -/
def IsValid (D : GeneratorCoordinateData) : Prop :=
  D.cubic.IsValid ∧
    (∀ k, (D.powers k).center =
      (D.cubic.cell.val : ℚ) + D.cubic.midpoint - (generatorKnot k : ℚ)) ∧
    ∀ k, (D.powers k).radius = D.cubic.width / 2

instance (D : GeneratorCoordinateData) : Decidable D.IsValid := by
  unfold IsValid
  infer_instance

/-- Each selected signed power family satisfies genuine root and error checks. -/
theorem powers_valid (D : GeneratorCoordinateData) (k : Fin 53) :
    (D.powers k).IsValid :=
  GeneratorPowerTaylorData.signedFamily_valid
    (fun j ↦ generatorPowerCache_valid (D.roots j).1 (D.roots j).2) D.negative k

end GeneratorCoordinateData

end PartialBalayage.Maximal.Square
