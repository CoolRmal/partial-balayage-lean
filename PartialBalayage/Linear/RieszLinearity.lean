/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.BoundedVectorMultiplier
public import PartialBalayage.Linear.PoissonFiniteUniformBounds
public import PartialBalayage.Linear.FourierOperatorBridge

/-!
# The full actual Riesz vector as a bounded linear map

The genuine Euclidean-vector multiplier gives the complex-linear Riesz map.
Its restriction to complexified real inputs is a real-linear contraction and
agrees with the independently specified full-vector Fourier operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²V" => Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure D)

/-- The full actual complex Riesz transform as a bounded complex-linear map. -/
def rieszL2CLM (n : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  boundedVectorMultiplierL2CLM rieszSymbol measurable_rieszSymbol 1
    (fun ξ ↦ by simpa using norm_rieszSymbol_le ξ)

theorem rieszL2CLM_apply (f : L²ℂ) : rieszL2CLM n f = rieszL2 f := rfl

theorem opNNNorm_rieszL2CLM_le : ‖rieszL2CLM n‖₊ ≤ 1 :=
  opNNNorm_boundedVectorMultiplierL2CLM_le rieszSymbol measurable_rieszSymbol 1
    (fun ξ ↦ by simpa using norm_rieszSymbol_le ξ)

theorem rieszL2_sub (f g : L²ℂ) : rieszL2 (f - g) = rieszL2 f - rieszL2 g := by
  simpa only [rieszL2CLM_apply] using (rieszL2CLM n).map_sub f g

/-- The actual full Riesz vector on real inputs, as a bounded real-linear map. -/
def rieszRealL2CLM (n : ℕ) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp (EuclideanSpace ℂ (Fin n)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (rieszL2CLM n).restrictScalars ℝ ∘L Complex.ofRealCLM.compLpL 2 volume

theorem rieszRealL2CLM_apply (f : L²ℝ) :
    rieszRealL2CLM n f = rieszL2 (Complex.ofRealCLM.compLp f) := rfl

theorem norm_rieszRealL2CLM_le (f : L²ℝ) : ‖rieszRealL2CLM n f‖ ≤ ‖f‖ := by
  rw [rieszRealL2CLM_apply]
  exact (norm_rieszL2_le _).trans_eq (norm_complexifyL2 f)

theorem opNNNorm_rieszRealL2CLM_le : ‖rieszRealL2CLM n‖₊ ≤ 1 := by
  apply ContinuousLinearMap.opNNNorm_le_bound
  intro f
  rw [one_mul]
  exact_mod_cast norm_rieszRealL2CLM_le f

/-- The independently defined actual Fourier operator equals this real-linear map. -/
theorem rieszFourierOperator_eq_rieszRealL2CLM (f : L²ℝ) :
    rieszFourierOperator f = rieszRealL2CLM n f :=
  rieszFourierOperator_eq_rieszL2 f

end PartialBalayage.Linear
