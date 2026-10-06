/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.ComplexTableDefinitions
public import PartialBalayage.Linear.FourierOperatorBridge
public import PartialBalayage.Linear.RieszLinearity

/-!
# Identifying the independently specified complex Riesz vector

The true bounded full-vector Fourier multiplier agrees with the independently
defined complex-input table operator, including the zero frequency.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PartialBalayage.Linear

/-- The independent complex Riesz table operator equals the genuine full-vector multiplier. -/
theorem complexRieszFourierOperator_eq_rieszL2CLM {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    complexRieszFourierOperator f = rieszL2CLM n f := by
  exact canonicalL2FourierOperator_eq_vectorMultiplier rieszSymbol measurable_rieszSymbol
    norm_rieszSymbol_le f

end PartialBalayage.Linear
