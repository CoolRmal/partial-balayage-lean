/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonFourier
public import PartialBalayage.Linear.FourierL1L2
public import PartialBalayage.Linear.OperatorMultiplier

/-!
# Genuine Poisson convolution on Hilbert `L²`

The actual normalized spatial probability average defines a contraction on `L²`.
Its construction uses full squared mass, so no compact support or convolution certificate
is imposed on an input function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Convolution

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure X)

/-- The genuine spatial Poisson average of a Banach-valued function. -/
def poissonConvolution (t : ℝ) (f : X → E) (x : X) : E :=
  ∫ y, f (x - y) ∂(PartialBalayage.poissonKernelMeasure n t)

omit [CompleteSpace E] in
/-- The squared norm of any actual probability average satisfies the extended Jensen bound. -/
theorem enorm_integral_sq_le_lintegral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (g : Y → E) (hg : AEStronglyMeasurable g μ) :
    ‖∫ y, g y ∂μ‖ₑ ^ (2 : ℕ) ≤ ∫⁻ y, ‖g y‖ₑ ^ (2 : ℕ) ∂μ := by
  have hbound : ‖∫ y, g y ∂μ‖ₑ ≤ eLpNorm g 2 μ :=
    (enorm_integral_le_lintegral_enorm g).trans
      ((lintegral_enorm_le_eLpNorm_one).trans
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)))
  calc
    _ ≤ eLpNorm g 2 μ ^ (2 : ℕ) := pow_le_pow_left' hbound 2
    _ = _ := by simpa [ENNReal.rpow_two] using
        eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hg

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Translation invariance and the genuine probability normalization give the exact squared mass. -/
theorem lintegral_poisson_translated_sq {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫⁻ x : X, ∫⁻ y, ‖f (x - y)‖ₑ ^ (2 : ℕ)
      ∂(PartialBalayage.poissonKernelMeasure n t)) = ‖f‖ₑ ^ (2 : ℕ) := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hmeas : Measurable (fun p : X × X ↦ ‖f (p.1 - p.2)‖ₑ ^ (2 : ℕ)) :=
    ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).enorm.pow_const 2
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hshift (y : X) : (∫⁻ x : X, ‖f (x - y)‖ₑ ^ (2 : ℕ)) =
      ∫⁻ x : X, ‖f x‖ₑ ^ (2 : ℕ) := by
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure X) (-y)).lintegral_comp
        ((Lp.stronglyMeasurable f).enorm.pow_const 2)
  simp_rw [hshift]
  rw [lintegral_const, measure_univ, mul_one, Lp.enorm_def]
  symm
  simpa [ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) (Lp.aestronglyMeasurable f)

omit [CompleteSpace E] in
/-- Actual Poisson averaging contracts the full extended squared mass. -/
theorem lintegral_poissonConvolution_sq_le {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫⁻ x : X, ‖poissonConvolution t f x‖ₑ ^ (2 : ℕ)) ≤ ‖f‖ₑ ^ (2 : ℕ) := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  calc
    _ ≤ ∫⁻ x : X, ∫⁻ y, ‖f (x - y)‖ₑ ^ (2 : ℕ)
        ∂(PartialBalayage.poissonKernelMeasure n t) := by
      apply lintegral_mono
      intro x
      exact enorm_integral_sq_le_lintegral _ _
        ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).aestronglyMeasurable
    _ = _ := lintegral_poisson_translated_sq ht f

omit [CompleteSpace E] in
/-- The actual Poisson average of every `L²` class is genuinely in `L²`. -/
theorem memLp_poissonConvolution {t : ℝ} (ht : 0 < t) (f : L²) :
    MemLp (poissonConvolution t f) 2 volume := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hstrong : StronglyMeasurable (poissonConvolution t f) :=
    ((Lp.stronglyMeasurable f).comp_measurable
      (show Measurable (fun p : X × X ↦ p.1 - p.2) by fun_prop)).integral_prod_right'
  have hmeas := hstrong.aestronglyMeasurable (μ := volume)
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hmeas).mpr ?_
  simpa [ENNReal.rpow_two] using
    (lintegral_poissonConvolution_sq_le ht f).trans_lt (by finiteness)

/-- The genuine `L²` class of the normalized spatial Poisson convolution. -/
def poissonConvolutionL2 {t : ℝ} (ht : 0 < t) (f : L²) : L² :=
  (memLp_poissonConvolution ht f).toLp (poissonConvolution t f)

omit [CompleteSpace E] in
/-- The actual `L²` convolution class has its ordinary probability-average representative. -/
theorem poissonConvolutionL2_ae {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonConvolutionL2 ht f =ᵐ[volume] poissonConvolution t f :=
  (memLp_poissonConvolution ht f).coeFn_toLp

omit [CompleteSpace E] in
/-- The exact spatial Poisson convolution is a genuine `L²` contraction. -/
theorem norm_poissonConvolutionL2_le {t : ℝ} (ht : 0 < t) (f : L²) :
    ‖poissonConvolutionL2 ht f‖ ≤ ‖f‖ := by
  have hsquare : ‖poissonConvolutionL2 ht f‖ₑ ^ (2 : ℕ) ≤ ‖f‖ₑ ^ (2 : ℕ) := by
    rw [Lp.enorm_def]
    have heq : eLpNorm (poissonConvolutionL2 ht f) 2 volume ^ (2 : ℕ) =
        ∫⁻ x : X, ‖poissonConvolutionL2 ht f x‖ₑ ^ (2 : ℕ) := by
      simpa [ENNReal.rpow_two] using eLpNorm_nnreal_pow_eq_lintegral
        (p := 2) (by norm_num) (Lp.aestronglyMeasurable (poissonConvolutionL2 ht f))
    rw [heq]
    have hae : (∫⁻ x : X, ‖poissonConvolutionL2 ht f x‖ₑ ^ (2 : ℕ)) =
        ∫⁻ x : X, ‖poissonConvolution t f x‖ₑ ^ (2 : ℕ) :=
      lintegral_congr_ae ((poissonConvolutionL2_ae ht f).fun_comp
        (fun v : E ↦ ‖v‖ₑ ^ (2 : ℕ)))
    rw [hae]
    exact lintegral_poissonConvolution_sq_le ht f
  have h := (ENNReal.toReal_mono (by finiteness) hsquare)
  simp only [ENNReal.toReal_pow, toReal_enorm] at h
  nlinarith [norm_nonneg f, norm_nonneg (poissonConvolutionL2 ht f)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Almost every point has a genuinely integrable translated input under Poisson averaging. -/
theorem ae_integrable_poisson_translates {t : ℝ} (ht : 0 < t) (f : L²) :
    ∀ᵐ x ∂volume, Integrable (fun y ↦ f (x - y))
      (PartialBalayage.poissonKernelMeasure n t) := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hsq : (∫⁻ x : X, ∫⁻ y, ‖f (x - y)‖ₑ ^ (2 : ℕ)
      ∂(PartialBalayage.poissonKernelMeasure n t)) ≠ ⊤ := by
    rw [lintegral_poisson_translated_sq ht f]
    finiteness
  have hmeas : Measurable (fun p : X × X ↦ ‖f (p.1 - p.2)‖ₑ ^ (2 : ℕ)) :=
    ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).enorm.pow_const 2
  filter_upwards [ae_lt_top hmeas.lintegral_prod_right' hsq] with x hx
  have hpoint : AEStronglyMeasurable (fun y ↦ f (x - y))
      (PartialBalayage.poissonKernelMeasure n t) :=
    ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).aestronglyMeasurable
  have h2 : MemLp (fun y ↦ f (x - y)) 2
      (PartialBalayage.poissonKernelMeasure n t) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) (by norm_num) hpoint).mpr
    simpa [ENNReal.rpow_two] using hx
  exact h2.integrable (by norm_num)

omit [CompleteSpace E] in
/-- The genuine probability average respects equality of inputs almost everywhere. -/
theorem poissonConvolution_congr (t : ℝ) {f g : X → E} (hfg : f =ᵐ[volume] g) :
    poissonConvolution t f = poissonConvolution t g := by
  funext x
  apply integral_congr_ae
  exact (withDensity_absolutelyContinuous volume
    (fun y ↦ ENNReal.ofReal (PartialBalayage.poissonKernel n t y))).ae_le
      (hfg.comp_tendsto (volume.measurePreserving_sub_left x).quasiMeasurePreserving.tendsto_ae)

omit [CompleteSpace E] in
/-- Actual spatial Poisson averaging is additive on `L²` classes. -/
theorem poissonConvolutionL2_add {t : ℝ} (ht : 0 < t) (f g : L²) :
    poissonConvolutionL2 ht (f + g) = poissonConvolutionL2 ht f + poissonConvolutionL2 ht g := by
  have hsource := poissonConvolution_congr t (Lp.coeFn_add f g)
  apply Lp.ext
  filter_upwards [poissonConvolutionL2_ae ht (f + g), poissonConvolutionL2_ae ht f,
    poissonConvolutionL2_ae ht g, ae_integrable_poisson_translates ht f,
    ae_integrable_poisson_translates ht g,
    Lp.coeFn_add (poissonConvolutionL2 ht f) (poissonConvolutionL2 ht g)]
    with x hsum hf hg hfi hgi hadd
  rw [hsum, hadd, Pi.add_apply, hf, hg, hsource]
  exact integral_add hfi hgi

omit [CompleteSpace E] in
/-- Actual spatial Poisson averaging respects real scalar multiplication. -/
theorem poissonConvolutionL2_smul {t : ℝ} (ht : 0 < t) (c : ℝ) (f : L²) :
    poissonConvolutionL2 ht (c • f) = c • poissonConvolutionL2 ht f := by
  have hsource := poissonConvolution_congr t (Lp.coeFn_smul c f)
  apply Lp.ext
  filter_upwards [poissonConvolutionL2_ae ht (c • f), poissonConvolutionL2_ae ht f,
    Lp.coeFn_smul c (poissonConvolutionL2 ht f)] with x hcf hf hsmul
  rw [hcf, hsmul, Pi.smul_apply, hf, hsource]
  exact integral_smul c (fun y ↦ f (x - y))

/-- The actual normalized spatial Poisson convolution is a bounded real linear `L²` operator. -/
def poissonConvolutionL2CLM {t : ℝ} (ht : 0 < t) : L² →L[ℝ] L² :=
  ({ toFun := poissonConvolutionL2 ht
     map_add' := poissonConvolutionL2_add ht
     map_smul' := poissonConvolutionL2_smul ht } : L² →ₗ[ℝ] L²).mkContinuous 1
    (fun f ↦ by
      change ‖poissonConvolutionL2 ht f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact norm_poissonConvolutionL2_le ht f)

end PartialBalayage.Linear
