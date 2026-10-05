/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupTimeContinuity
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Countable rational-time bounds for the actual semigroup maximal functions

A countable intersection makes an almost-everywhere estimate simultaneous for all
positive rational times. The proved continuity of the original convolutions extends
it to every positive real time. Thus the actual all-time supremum inherits the bound.
The same argument identifies each maximal function with a countable rational supremum.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PartialBalayage

/-- A positive-time continuous function inherits an upper bound from positive rational times. -/
theorem le_of_positive_rational_bound {A : Type*} [LinearOrder A] [TopologicalSpace A]
    [OrderTopology A] (F : ℝ → A) (C : A)
    (hc : ∀ t, 0 < t → ContinuousAt F t)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → F q ≤ C) {t : ℝ} (ht : 0 < t) : F t ≤ C := by
  by_contra h
  have hnear : ∀ᶠ s in 𝓝 t, C < F s :=
    (hc t ht).eventually (Ioi_mem_nhds (lt_of_not_ge h))
  have hpos : ∀ᶠ s in 𝓝 t, 0 < s := Ioi_mem_nhds ht
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.mem_nhds (hpos.and hnear)
  exact not_lt_of_ge (hb q hq.1) hq.2

/-- Fixed-rational-time almost-everywhere estimates become simultaneous all-positive-time
estimates. The condition on spatial points need not be measurable. -/
theorem ae_all_positive_times_le_of_rational_bounds {X A : Type*} [MeasurableSpace X]
    {μ : Measure X} [LinearOrder A] [TopologicalSpace A] [OrderTopology A]
    (F : ℝ → X → A) (P : X → Prop) (C : X → A)
    (hc : ∀ x t, 0 < t → ContinuousAt (fun s ↦ F s x) t)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ x ∂μ, P x → F q x ≤ C x) :
    ∀ᵐ x ∂μ, P x → ∀ t : ℝ, 0 < t → F t x ≤ C x := by
  have hall : ∀ᵐ x ∂μ, ∀ q : ℚ, 0 < (q : ℝ) → P x → F q x ≤ C x := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · exact (hb q hq).mono (fun x hx _ ↦ hx)
    · exact Eventually.of_forall (fun x hx ↦ False.elim (hq hx))
  filter_upwards [hall] with x hx
  intro hp t ht
  exact le_of_positive_rational_bound (fun s ↦ F s x) (C x) (hc x)
    (fun q hq ↦ hx q hq hp) ht

/-- The heat maximal integral is the nonnegative real heat convolution of the input norm. -/
theorem lintegral_heatKernel_mul_enorm_eq {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ y, ENNReal.ofReal (heatKernel n t (x - y)) * ‖f y‖ₑ) =
      ENNReal.ofReal (heatConvolution t (fun y ↦ ‖f y‖) x) := by
  rw [heatConvolution, ofReal_integral_eq_lintegral_ofReal
    (integrable_heatKernel_mul n ht hf.norm x)
    (Eventually.of_forall (fun y ↦ mul_nonneg (heatKernel_pos n ht _).le (norm_nonneg _)))]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (heatKernel_pos n ht _).le, ofReal_norm]

/-- The Poisson maximal integral is the nonnegative real convolution of the input norm. -/
theorem lintegral_poissonKernel_mul_enorm_eq {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ y, ENNReal.ofReal (poissonKernel n t (x - y)) * ‖f y‖ₑ) =
      ENNReal.ofReal (poissonConvolution t (fun y ↦ ‖f y‖) x) := by
  rw [poissonConvolution, ofReal_integral_eq_lintegral_ofReal
    (integrable_poissonKernel_mul n ht hf.norm x)
    (Eventually.of_forall (fun y ↦ mul_nonneg (poissonKernel_pos n ht _).le (norm_nonneg _)))]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (poissonKernel_pos n ht _).le, ofReal_norm]

/-- For every integrable input, the actual heat maximal function is a countable supremum. -/
theorem heatMaximalFunction_eq_iSup_rational {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatMaximalFunction f x = ⨆ (q : ℚ) (_ : 0 < (q : ℝ)),
      ENNReal.ofReal (heatConvolution q (fun y ↦ ‖f y‖) x) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    rw [lintegral_heatKernel_mul_enorm_eq ht hf x]
    apply le_of_positive_rational_bound
      (fun s ↦ ENNReal.ofReal (heatConvolution s (fun y ↦ ‖f y‖) x))
    · intro s hs
      exact ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_heatConvolution hf.norm hs x)
    · intro q hq
      exact le_iSup_of_le q (le_iSup_of_le hq le_rfl)
    · exact ht
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    rw [← lintegral_heatKernel_mul_enorm_eq hq hf x]
    exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hq le_rfl)

/-- For every integrable input, the actual Poisson maximal function is a countable supremum. -/
theorem poissonMaximalFunction_eq_iSup_rational {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    poissonMaximalFunction f x = ⨆ (q : ℚ) (_ : 0 < (q : ℝ)),
      ENNReal.ofReal (poissonConvolution q (fun y ↦ ‖f y‖) x) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    rw [lintegral_poissonKernel_mul_enorm_eq ht hf x]
    apply le_of_positive_rational_bound
      (fun s ↦ ENNReal.ofReal (poissonConvolution s (fun y ↦ ‖f y‖) x))
    · intro s hs
      exact ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_poissonConvolution hf.norm hs x)
    · intro q hq
      exact le_iSup_of_le q (le_iSup_of_le hq le_rfl)
    · exact ht
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    rw [← lintegral_poissonKernel_mul_enorm_eq hq hf x]
    exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hq le_rfl)

/-- Actual real heat convolutions inherit an all-time estimate from fixed rational estimates. -/
theorem ae_all_heatConvolution_le_of_rational_bounds {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (P : EuclideanSpace ℝ (Fin n) → Prop) (C : EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ x, P x → heatConvolution q f x ≤ C x) :
    ∀ᵐ x, P x → ∀ t : ℝ, 0 < t → heatConvolution t f x ≤ C x :=
  ae_all_positive_times_le_of_rational_bounds (fun t x ↦ heatConvolution t f x) P C
    (fun x _ ht ↦ continuousAt_heatConvolution hf ht x) hb

/-- Actual real Poisson convolutions inherit an all-time estimate from fixed rational estimates. -/
theorem ae_all_poissonConvolution_le_of_rational_bounds {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (P : EuclideanSpace ℝ (Fin n) → Prop) (C : EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ x, P x → poissonConvolution q f x ≤ C x) :
    ∀ᵐ x, P x → ∀ t : ℝ, 0 < t → poissonConvolution t f x ≤ C x :=
  ae_all_positive_times_le_of_rational_bounds (fun t x ↦ poissonConvolution t f x) P C
    (fun x _ ht ↦ continuousAt_poissonConvolution hf ht x) hb

/-- A rational-time bound for the input norm controls the actual all-time heat maximal function. -/
theorem ae_heatMaximalFunction_le_of_rational_bounds {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (P : EuclideanSpace ℝ (Fin n) → Prop) (C : EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ x, P x →
      heatConvolution q (fun y ↦ ‖f y‖) x ≤ C x) :
    ∀ᵐ x, P x → heatMaximalFunction f x ≤ ENNReal.ofReal (C x) := by
  have hall := ae_all_heatConvolution_le_of_rational_bounds hf.norm P C hb
  filter_upwards [hall] with x hx
  intro hp
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  rw [lintegral_heatKernel_mul_enorm_eq ht hf x]
  exact ENNReal.ofReal_le_ofReal (hx hp t ht)

/-- A rational-time bound for the input norm controls the actual Poisson maximal function. -/
theorem ae_poissonMaximalFunction_le_of_rational_bounds {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (P : EuclideanSpace ℝ (Fin n) → Prop) (C : EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ x, P x →
      poissonConvolution q (fun y ↦ ‖f y‖) x ≤ C x) :
    ∀ᵐ x, P x → poissonMaximalFunction f x ≤ ENNReal.ofReal (C x) := by
  have hall := ae_all_poissonConvolution_le_of_rational_bounds hf.norm P C hb
  filter_upwards [hall] with x hx
  intro hp
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  rw [lintegral_poissonKernel_mul_enorm_eq ht hf x]
  exact ENNReal.ofReal_le_ofReal (hx hp t ht)

/-- For nonnegative input the rational heat estimates apply directly to the input. -/
theorem ae_heatMaximalFunction_le_of_nonneg_rational_bounds {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f) (hf0 : ∀ᵐ y, 0 ≤ f y)
    (P : EuclideanSpace ℝ (Fin n) → Prop) (C : EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ x, P x → heatConvolution q f x ≤ C x) :
    ∀ᵐ x, P x → heatMaximalFunction f x ≤ ENNReal.ofReal (C x) := by
  apply ae_heatMaximalFunction_le_of_rational_bounds hf P C
  intro q hq
  filter_upwards [hb q hq] with x hx
  have heq : heatConvolution q (fun y ↦ ‖f y‖) x = heatConvolution q f x := by
    apply integral_congr_ae
    filter_upwards [hf0] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg hy]
  rwa [heq]

/-- For nonnegative input the rational Poisson estimates apply directly to the input. -/
theorem ae_poissonMaximalFunction_le_of_nonneg_rational_bounds {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f) (hf0 : ∀ᵐ y, 0 ≤ f y)
    (P : EuclideanSpace ℝ (Fin n) → Prop) (C : EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ x, P x → poissonConvolution q f x ≤ C x) :
    ∀ᵐ x, P x → poissonMaximalFunction f x ≤ ENNReal.ofReal (C x) := by
  apply ae_poissonMaximalFunction_le_of_rational_bounds hf P C
  intro q hq
  filter_upwards [hb q hq] with x hx
  have heq : poissonConvolution q (fun y ↦ ‖f y‖) x = poissonConvolution q f x := by
    apply integral_congr_ae
    filter_upwards [hf0] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg hy]
  rwa [heq]

end PartialBalayage
