/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith

/-!
# The elementary Kato inequality for positive averaging

A vector of norm at most one that supports the norm at `u` bounds the norm defect under averaging
by the corresponding inner-product defect. The proof uses Cauchy–Schwarz, monotonicity of the
Bochner integral, and the inner-product/integral identity. No semigroup or generator is assumed.

The unnormalized inequality holds for an arbitrary measure. Probability measures give the
integrated defect form. A nonnegative scalar kernel is handled by its weighted vector field.
Complex Hilbert spaces can be regarded as real inner product spaces for these results.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [CompleteSpace E]
variable {μ : Measure X} {v : X → E} {u w : E}

/-- Supporting the norm at `u` bounds its defect under integration by an inner-product defect. -/
theorem kato_averaging (hv : Integrable v μ) (hw : ‖w‖ ≤ 1)
    (hu : ⟪w, u⟫_ℝ = ‖u‖) :
    ‖u‖ - ∫ x, ‖v x‖ ∂μ ≤ ⟪w, u - ∫ x, v x ∂μ⟫_ℝ := by
  rw [inner_sub_right, hu, ← integral_inner hv w]
  apply sub_le_sub_left
  apply integral_mono (hv.const_inner w) hv.norm
  intro x
  exact (real_inner_le_norm w (v x)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (v x)))

/-- For probability averaging, the Kato inequality also compares the integrated defects. -/
theorem kato_probability_averaging [IsProbabilityMeasure μ] (hv : Integrable v μ)
    (hw : ‖w‖ ≤ 1) (hu : ⟪w, u⟫_ℝ = ‖u‖) :
    (∫ x, ‖u‖ - ‖v x‖ ∂μ) ≤ ∫ x, ⟪w, u - v x⟫_ℝ ∂μ := by
  have hleft : (∫ x, ‖u‖ - ‖v x‖ ∂μ) = ‖u‖ - ∫ x, ‖v x‖ ∂μ := by
    rw [integral_sub (integrable_const _) hv.norm]
    simp only [integral_const, probReal_univ, one_smul]
  have hright : (∫ x, ⟪w, u - v x⟫_ℝ ∂μ) = ⟪w, u - ∫ x, v x ∂μ⟫_ℝ := by
    simp_rw [inner_sub_right]
    rw [integral_sub (integrable_const _) (hv.const_inner w), integral_inner hv w]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hleft, hright]
  exact kato_averaging hv hw hu

/-- A nonnegative scalar kernel gives the same Kato inequality for the weighted vector average. -/
theorem kato_weighted_averaging {k : X → ℝ}
    (hkv : Integrable (fun x ↦ k x • v x) μ) (hk : ∀ᵐ x ∂μ, 0 ≤ k x)
    (hw : ‖w‖ ≤ 1) (hu : ⟪w, u⟫_ℝ = ‖u‖) :
    ‖u‖ - ∫ x, k x * ‖v x‖ ∂μ ≤ ⟪w, u - ∫ x, k x • v x ∂μ⟫_ℝ := by
  have heq : (∫ x, ‖k x • v x‖ ∂μ) = ∫ x, k x * ‖v x‖ ∂μ := by
    apply integral_congr_ae
    filter_upwards [hk] with x hx
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx]
  simpa only [heq] using kato_averaging hkv hw hu

end PartialBalayage.Linear
