/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonNormEnergy

/-!
# The actual Poisson quadratic form in physical space

The genuine spatial quadratic defect is half the probability average of squared
increments. All product integrals are justified by actual `L²` integrability.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance poissonQuadraticSpatialRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonQuadraticSpatialScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)

/-- The genuine spatial increment product measure. -/
def poissonPairMeasure (t : ℝ) : Measure (D × D) :=
  volume.prod (PartialBalayage.poissonKernelMeasure n t)

omit [CompleteSpace E] in
/-- The physical squared norm of an actual Hilbert `L²` class integrates to its squared norm. -/
theorem poisson_integral_norm_sq (f : L²) : (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := Complex.reCLM.integral_comp_comm (L2.integrable_inner f f)
  simp only [Complex.reCLM_apply] at h
  calc
    _ = ∫ x, (inner ℂ (f x) (f x)).re := by
      apply integral_congr_ae
      filter_upwards with x
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (f x)).symm
    _ = (inner ℂ f f).re := by rw [L2.inner_def, h]
    _ = _ := inner_self_eq_norm_sq (𝕜 := ℂ) f

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The first-coordinate pullback genuinely belongs to product `L²`. -/
theorem memLp_poisson_first_pair {t : ℝ} (ht : 0 < t) (f : L²) :
    MemLp (fun p : D × D ↦ f p.1) 2 (poissonPairMeasure t) := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  exact (Lp.memLp f).comp_fst _

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The actual translated pullback genuinely belongs to product `L²`. -/
theorem memLp_poisson_translated_pair {t : ℝ} (ht : 0 < t) (f : L²) :
    MemLp (fun p : D × D ↦ f (p.1 - p.2)) 2 (poissonPairMeasure t) := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hm : StronglyMeasurable (fun p : D × D ↦ f (p.1 - p.2)) :=
    (Lp.stronglyMeasurable f).comp_measurable (by fun_prop)
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hm.aestronglyMeasurable).mpr
  have hfin : (∫⁻ p : D × D, ‖f (p.1 - p.2)‖ₑ ^ (2 : ℕ)
      ∂poissonPairMeasure t) < ⊤ := by
    rw [poissonPairMeasure, lintegral_prod _ (hm.enorm.pow_const 2).aemeasurable,
      lintegral_poisson_translated_sq ht]
    finiteness
  simpa [ENNReal.rpow_two] using hfin

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The actual increment is square integrable over the full physical product measure. -/
theorem integrable_poisson_increment_sq {t : ℝ} (ht : 0 < t) (f : L²) :
    Integrable (fun p : D × D ↦ ‖f p.1 - f (p.1 - p.2)‖ ^ 2)
      (poissonPairMeasure t) :=
  ((memLp_poisson_first_pair ht f).sub
    (memLp_poisson_translated_pair ht f)).integrable_norm_pow (by norm_num)

omit [CompleteSpace E] in
/-- The physical product inner product is integrable by actual product `L²` membership. -/
theorem integrable_poisson_pair_inner {t : ℝ} (ht : 0 < t) (f : L²) :
    Integrable (fun p : D × D ↦ inner ℂ (f p.1) (f (p.1 - p.2)))
      (poissonPairMeasure t) := by
  let F₀ := (memLp_poisson_first_pair ht f).toLp (fun p : D × D ↦ f p.1)
  let F₁ := (memLp_poisson_translated_pair ht f).toLp (fun p : D × D ↦ f (p.1 - p.2))
  apply (L2.integrable_inner F₀ F₁).congr
  filter_upwards [(memLp_poisson_first_pair ht f).coeFn_toLp,
    (memLp_poisson_translated_pair ht f).coeFn_toLp] with p h₀ h₁
  rw [h₀, h₁]

omit [CompleteSpace E] in
/-- Actual probability normalization gives the first-coordinate squared mass. -/
theorem integral_poisson_first_pair_sq {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫ p : D × D, ‖f p.1‖ ^ 2 ∂poissonPairMeasure t) = ‖f‖ ^ 2 := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hi := (memLp_poisson_first_pair ht f).integrable_norm_pow (by norm_num : 2 ≠ 0)
  rw [poissonPairMeasure, integral_prod _ hi]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact poisson_integral_norm_sq f

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- Translation invariance gives the actual translated-coordinate squared mass. -/
theorem integral_poisson_translated_pair_sq {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫ p : D × D, ‖f (p.1 - p.2)‖ ^ 2 ∂poissonPairMeasure t) = ‖f‖ ^ 2 := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hm : StronglyMeasurable (fun p : D × D ↦ f (p.1 - p.2)) :=
    (Lp.stronglyMeasurable f).comp_measurable (by fun_prop)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun p ↦ sq_nonneg _)) (hm.norm.pow 2).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [poissonPairMeasure, lintegral_prod _ (hm.enorm.pow_const 2).aemeasurable,
    lintegral_poisson_translated_sq ht, ENNReal.toReal_pow, toReal_enorm]

/-- Actual Poisson averaging evaluates the full physical product inner product. -/
theorem integral_poisson_pair_inner_re {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫ p : D × D, (inner ℂ (f p.1) (f (p.1 - p.2))).re ∂poissonPairMeasure t) =
      (inner ℂ f (poissonConvolutionL2 ht f)).re := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  have hi := Complex.reCLM.integrable_comp (integrable_poisson_pair_inner ht f)
  have hire := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner f (poissonConvolutionL2 ht f))
  simp only [Complex.reCLM_apply] at hire hi
  rw [poissonPairMeasure, integral_prod _ hi, L2.inner_def, ← hire]
  apply integral_congr_ae
  filter_upwards [ae_integrable_poisson_translates ht f, poissonConvolutionL2_ae ht f]
    with x hint hP
  rw [hP, poissonConvolution, ← integral_inner hint (f x)]
  have hx := Complex.reCLM.integral_comp_comm (hint.const_inner (f x) (𝕜 := ℂ))
  simpa only [Complex.reCLM_apply] using hx

/-- The genuine full spatial squared increment average is twice the Poisson energy defect. -/
theorem integral_poisson_increment_sq {t : ℝ} (ht : 0 < t) (f : L²) :
    (∫ p : D × D, ‖f p.1 - f (p.1 - p.2)‖ ^ 2 ∂poissonPairMeasure t) =
      2 * (‖f‖ ^ 2 - (inner ℂ f (poissonConvolutionL2 ht f)).re) := by
  have h₀ := (memLp_poisson_first_pair ht f).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have h₁ := (memLp_poisson_translated_pair ht f).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hi := Complex.reCLM.integrable_comp (integrable_poisson_pair_inner ht f)
  simp only [Complex.reCLM_apply] at hi
  simp_rw [norm_sub_sq (𝕜 := ℂ), RCLike.re_eq_complex_re]
  have hadd := integral_add (h₀.sub (hi.const_mul 2)) h₁
  simp only [Pi.sub_apply] at hadd
  rw [hadd]
  have hsub := integral_sub h₀ (hi.const_mul 2)
  dsimp only at hsub
  rw [hsub, integral_const_mul, integral_poisson_first_pair_sq ht,
    integral_poisson_translated_pair_sq ht, integral_poisson_pair_inner_re ht]
  ring

/-- The genuine quadratic defect has the exact averaged-increment normalization. -/
theorem poissonQuadraticDefect_eq_increment_integral {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonQuadraticDefect ht f = (2 * t)⁻¹ *
      ∫ p : D × D, ‖f p.1 - f (p.1 - p.2)‖ ^ 2 ∂poissonPairMeasure t := by
  rw [integral_poisson_increment_sq ht, poissonQuadraticDefect, poissonQuotientL2,
    inner_smul_right, inner_sub_right, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_re]
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  rw [hself]
  field_simp

end PartialBalayage.Linear
