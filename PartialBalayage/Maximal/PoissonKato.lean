/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.PoissonKernel
public import PartialBalayage.Linear.KatoAveraging

/-!
# The norm-defect inequality for actual Poisson averaging

The density is the exact Poisson kernel, whose probability normalization has been proved.
A supporting vector for the norm bounds the norm defect of its actual vector average.
The statements apply to real Hilbert spaces, including complex Hilbert spaces restricted
to the real scalars.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace PartialBalayage

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Poisson convolution is the actual vector average against the genuine kernel measure. -/
def poissonAverage (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → E)
    (x : EuclideanSpace ℝ (Fin n)) : E :=
  ∫ y, f (x - y) ∂(poissonKernelMeasure n t)

/-- A norm-supporting vector bounds the defect of an actual Poisson average. -/
theorem poisson_norm_defect_le {t : ℝ} (f : EuclideanSpace ℝ (Fin n) → E)
    (x : EuclideanSpace ℝ (Fin n))
    (hf : Integrable (fun y ↦ f (x - y)) (poissonKernelMeasure n t)) {w : E}
    (hw : ‖w‖ ≤ 1) (hsupport : ⟪w, f x⟫ = ‖f x‖) :
    ‖f x‖ - (∫ y, ‖f (x - y)‖ ∂(poissonKernelMeasure n t)) ≤
      ⟪w, f x - poissonAverage t f x⟫ :=
  Linear.kato_averaging hf hw hsupport

/-- The genuine positive-height Poisson probability kernel satisfies the integrated Kato step. -/
theorem poisson_kato_averaging {t : ℝ} (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) → E) (x : EuclideanSpace ℝ (Fin n))
    (hf : Integrable (fun y ↦ f (x - y)) (poissonKernelMeasure n t)) {w : E}
    (hw : ‖w‖ ≤ 1) (hsupport : ⟪w, f x⟫ = ‖f x‖) :
    (∫ y, ‖f x‖ - ‖f (x - y)‖ ∂(poissonKernelMeasure n t)) ≤
      ∫ y, ⟪w, f x - f (x - y)⟫ ∂(poissonKernelMeasure n t) := by
  have : IsProbabilityMeasure (poissonKernelMeasure n t) :=
    isProbabilityMeasure_poissonKernelMeasure n ht
  exact Linear.kato_probability_averaging hf hw hsupport

end PartialBalayage
