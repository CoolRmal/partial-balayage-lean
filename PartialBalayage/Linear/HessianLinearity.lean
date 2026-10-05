/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.HessianMultiplier
public import PartialBalayage.Linear.BoundedVectorMultiplier

/-!
# The genuine Hessian multiplier as a bounded linear operator

The existing Frobenius-valued Hessian function agrees with the bounded Fourier multiplier
construction. Consequently it is complex linear, with operator norm at most one.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- The actual full Frobenius Hessian multiplier as a bounded complex linear map. -/
def hessianL2CLM (d : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin d × Fin d)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  boundedVectorMultiplierL2CLM hessianSymbol measurable_hessianSymbol 1
    (fun ξ ↦ by simpa using norm_hessianSymbol_le ξ)

/-- The bounded map acts by the previously defined actual Hessian operator. -/
theorem hessianL2CLM_apply
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    hessianL2CLM d f = hessianL2 f := by
  rfl

/-- The full Hessian's actual operator norm is at most one. -/
theorem opNNNorm_hessianL2CLM_le : ‖hessianL2CLM d‖₊ ≤ 1 :=
  opNNNorm_boundedVectorMultiplierL2CLM_le hessianSymbol measurable_hessianSymbol 1
    (fun ξ ↦ by simpa using norm_hessianSymbol_le ξ)

/-- The actual Hessian respects subtraction of complex L² inputs. -/
theorem hessianL2_sub
    (f g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    hessianL2 (f - g) = hessianL2 f - hessianL2 g := by
  simpa only [hessianL2CLM_apply] using (hessianL2CLM d).map_sub f g

/-- The actual Hessian respects complex scalar multiplication. -/
theorem hessianL2_smul (c : ℂ)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    hessianL2 (c • f) = c • hessianL2 f := by
  simpa only [hessianL2CLM_apply] using (hessianL2CLM d).map_smul c f

end PartialBalayage.Linear
