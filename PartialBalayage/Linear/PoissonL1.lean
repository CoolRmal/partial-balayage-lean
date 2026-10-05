/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonL2

/-!
# Genuine full-mass contraction of normalized Poisson averaging

Translation invariance and actual probability normalization give the exact first-moment
mass of translated inputs. Jensen's norm inequality then proves `L¹` contraction of the
actual spatial Poisson convolution class, including its integrability.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Actual translation invariance evaluates the full first-moment translated mass. -/
theorem lintegral_poisson_translated_enorm {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫⁻ x : D, ∫⁻ y, ‖f (x - y)‖ₑ ∂PartialBalayage.poissonKernelMeasure n t) =
      ∫⁻ x : D, ‖f x‖ₑ := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hm : Measurable (fun p : D × D ↦ ‖f (p.1 - p.2)‖ₑ) :=
    ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).enorm
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hshift (y : D) : (∫⁻ x : D, ‖f (x - y)‖ₑ) = ∫⁻ x : D, ‖f x‖ₑ := by
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure D) (-y)).lintegral_comp
        (Lp.stronglyMeasurable f).enorm
  simp_rw [hshift]
  rw [lintegral_const, measure_univ, mul_one]

omit [CompleteSpace E] in
/-- The actual normalized spatial Poisson average contracts full extended norm mass. -/
theorem lintegral_poissonConvolutionL2_enorm_le {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫⁻ x, ‖poissonConvolutionL2 ht f x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ := by
  have he : (∫⁻ x, ‖poissonConvolutionL2 ht f x‖ₑ) =
      ∫⁻ x, ‖poissonConvolution t f x‖ₑ :=
    lintegral_congr_ae ((poissonConvolutionL2_ae ht f).fun_comp (fun v : E ↦ ‖v‖ₑ))
  rw [he]
  calc
    _ ≤ ∫⁻ x : D, ∫⁻ y, ‖f (x - y)‖ₑ ∂PartialBalayage.poissonKernelMeasure n t := by
      apply lintegral_mono
      intro x
      exact enorm_integral_le_lintegral_enorm _
    _ = _ := lintegral_poisson_translated_enorm ht f

omit [CompleteSpace E] in
/-- Genuine `L¹` input produces a genuinely integrable actual `L²` Poisson average. -/
theorem integrable_poissonConvolutionL2_of_integrable {t : ℝ} (ht : 0 < t) (f : L²)
    (hf : Integrable (f : D → E)) : Integrable (poissonConvolutionL2 ht f : D → E) := by
  refine ⟨Lp.aestronglyMeasurable _, ?_⟩
  exact (lintegral_poissonConvolutionL2_enorm_le ht f).trans_lt hf.hasFiniteIntegral

omit [CompleteSpace E] in
/-- The actual normalized Poisson convolution contracts the ordinary full `L¹` norm. -/
theorem integral_norm_poissonConvolutionL2_le {t : ℝ} (ht : 0 < t) (f : L²)
    (hf : Integrable (f : D → E)) :
    (∫ x, ‖poissonConvolutionL2 ht f x‖) ≤ ∫ x, ‖f x‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
    integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_mono hf.hasFiniteIntegral.ne
    (lintegral_poissonConvolutionL2_enorm_le ht f)

end PartialBalayage.Linear
