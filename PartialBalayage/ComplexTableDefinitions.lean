/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.TableDefinitions

/-!
# Independent complex-input Riesz table operator

The complete complex Euclidean vector is specified directly by the actual
Fourier symbol. Its definition uses no analytical proof or certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform

namespace PartialBalayage

/-- The full complex-input Riesz vector, defined by its genuine Fourier symbol. -/
def complexRieszFourierOperator {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z • fourierRieszSymbol ξ) f

end PartialBalayage
