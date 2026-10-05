/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.NormalizedGeneratorCellCoefficients
public import PartialBalayage.Maximal.Square.GeneratorCoordinateData

/-!
# Equivalent actual cubic and coordinate checks using the normalized cache

Only evaluation speed changes: every cached row equals the original actual
coefficient, and each fast predicate is equivalent to its original predicate.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

namespace GeneratorCubicIntervalData

/-- Genuine original cubic checks, with the equivalent normalized coefficient cache. -/
def FastIsValid (D : GeneratorCubicIntervalData) : Prop :=
  0 < D.width ∧
    (∀ k b, D.centered k b =
      cubicAffineCoefficients (normalizedGeneratorCellCoefficients D.cell k) D.midpoint 1 b) ∧
    ∀ k b, |cubicBernsteinCoefficients
      (cubicAffineCoefficients (normalizedGeneratorCellCoefficients D.cell k) D.lower D.width) b| ≤
        D.bound k

instance (D : GeneratorCubicIntervalData) : Decidable D.FastIsValid := by
  unfold FastIsValid
  infer_instance

/-- Fast evaluation checks precisely the original mathematical validity predicate. -/
theorem fastIsValid_iff (D : GeneratorCubicIntervalData) : D.FastIsValid ↔ D.IsValid := by
  unfold FastIsValid IsValid
  rw [normalizedGeneratorCellCoefficients_eq]

/-- A checked fast certificate establishes the genuine original cubic validity. -/
theorem isValid_of_fast {D : GeneratorCubicIntervalData} (h : D.FastIsValid) : D.IsValid :=
  (fastIsValid_iff D).mp h

end GeneratorCubicIntervalData

namespace GeneratorCoordinateData

/-- The same actual coordinate predicate with equivalent cached cubic checks. -/
def FastIsValid (D : GeneratorCoordinateData) : Prop :=
  D.cubic.FastIsValid ∧
    (∀ k, (D.powers k).center =
      (D.cubic.cell.val : ℚ) + D.cubic.midpoint - (generatorKnot k : ℚ)) ∧
    ∀ k, (D.powers k).radius = D.cubic.width / 2

instance (D : GeneratorCoordinateData) : Decidable D.FastIsValid := by
  unfold FastIsValid
  infer_instance

/-- Fast coordinate checking has exactly the original mathematical meaning. -/
theorem fastIsValid_iff (D : GeneratorCoordinateData) : D.FastIsValid ↔ D.IsValid := by
  unfold FastIsValid IsValid
  rw [GeneratorCubicIntervalData.fastIsValid_iff]

/-- Fast checking establishes the genuine actual coordinate validity. -/
theorem isValid_of_fast {D : GeneratorCoordinateData} (h : D.FastIsValid) : D.IsValid :=
  (fastIsValid_iff D).mp h

end GeneratorCoordinateData

end PartialBalayage.Maximal.Square
