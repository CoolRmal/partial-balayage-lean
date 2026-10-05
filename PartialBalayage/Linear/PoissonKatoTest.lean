/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonGenerator

/-!
# Actual Poisson norm tests

The full spatial probability average satisfies the weighted norm-defect inequality on every
`L²` input. Genuine norm-supporting `L²` test vectors can be paired with the true isotropic
generator limit. No assumed semigroup or generator certificate occurs in these statements.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance poissonKatoTestRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonKatoTestScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := E) 2
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)

/-- A scalar weight and a supporting vector give the genuine Poisson norm-defect inequality. -/
theorem poisson_weighted_norm_defect_le {t : ℝ} (f : D → E) (x : D)
    (hf : Integrable (fun y ↦ f (x - y)) (PartialBalayage.poissonKernelMeasure n t))
    {a : ℝ} {w : E} (hw : ‖w‖ ≤ a) (hs : (inner ℂ w (f x)).re = a * ‖f x‖) :
    a * (‖f x‖ - ∫ y, ‖f (x - y)‖ ∂(PartialBalayage.poissonKernelMeasure n t)) ≤
      (inner ℂ w (f x - poissonConvolution t f x)).re := by
  have hi := hf.const_inner w (𝕜 := ℂ)
  have hire := Complex.reCLM.integral_comp_comm hi
  simp only [Complex.reCLM_apply] at hire
  have hb : (inner ℂ w (poissonConvolution t f x)).re ≤
      a * ∫ y, ‖f (x - y)‖ ∂(PartialBalayage.poissonKernelMeasure n t) := by
    rw [poissonConvolution, ← integral_inner hf w, ← hire, ← integral_const_mul]
    apply integral_mono_ae (Complex.reCLM.integrable_comp hi) (hf.norm.const_mul a)
    filter_upwards with y
    exact (re_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  rw [inner_sub_right, Complex.sub_re, hs]
  linarith

omit [CompleteSpace E] in
/-- The pointwise norm of an actual `L²` class is an actual real `L²` class. -/
def poissonNormL2 (f : L²) : L²ℝ :=
  (Lp.memLp f).norm.toLp (fun x ↦ ‖f x‖)

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The real norm class has its ordinary pointwise norm representative. -/
theorem poissonNormL2_ae (f : L²) : poissonNormL2 f =ᵐ[volume] (fun x ↦ ‖f x‖) :=
  (Lp.memLp f).norm.coeFn_toLp

/-- The actual scalar norm defect under normalized Poisson convolution. -/
def poissonNormDefectL2 {t : ℝ} (ht : 0 < t) (f : L²) : L²ℝ :=
  t⁻¹ • (poissonNormL2 f - poissonConvolutionL2 ht (poissonNormL2 f))

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The actual norm-defect class agrees with the ordinary spatial norm defect. -/
theorem poissonNormDefectL2_ae {t : ℝ} (ht : 0 < t) (f : L²) :
    ∀ᵐ x, poissonNormDefectL2 ht f x = t⁻¹ *
      (‖f x‖ - ∫ y, ‖f (x - y)‖ ∂(PartialBalayage.poissonKernelMeasure n t)) := by
  have hsource := poissonConvolution_congr t (poissonNormL2_ae f)
  filter_upwards [Lp.coeFn_smul t⁻¹
    (poissonNormL2 f - poissonConvolutionL2 ht (poissonNormL2 f)),
    Lp.coeFn_sub (poissonNormL2 f) (poissonConvolutionL2 ht (poissonNormL2 f)),
    poissonNormL2_ae f, poissonConvolutionL2_ae ht (poissonNormL2 f)]
    with x hs hsub hnorm hP
  change (t⁻¹ • (poissonNormL2 f - poissonConvolutionL2 ht (poissonNormL2 f))) x = _
  rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, hnorm, hP, hsource]
  rfl

/-- The true spatial difference quotient has its actual probability-average representative. -/
theorem poissonDifferenceQuotient_ae {t : ℝ} (ht : 0 < t) (U : H¹) :
    ∀ᵐ x, poissonDifferenceQuotient t U x = (t⁻¹ : ℂ) •
      (isotropicEnergyValue 2 U x - poissonConvolution t (isotropicEnergyValue 2 U) x) := by
  rw [poissonDifferenceQuotient, dite_eq_left ht]
  filter_upwards [Lp.coeFn_smul (t⁻¹ : ℂ)
    (isotropicEnergyValue 2 U - poissonConvolutionL2 ht (isotropicEnergyValue 2 U)),
    Lp.coeFn_sub (isotropicEnergyValue 2 U)
      (poissonConvolutionL2 ht (isotropicEnergyValue 2 U)),
    poissonConvolutionL2_ae ht (isotropicEnergyValue 2 U)] with x hs hsub hP
  rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, hP]

/-- Every actual norm-supporting `L²` test gives the integrated positive-height Kato inequality. -/
theorem poisson_kato_L2_test {t : ℝ} (ht : 0 < t) (U : H¹) (φ : L²ℝ) (W : L²)
    (hw : ∀ᵐ x, ‖W x‖ ≤ φ x)
    (hs : ∀ᵐ x, (inner ℂ (W x) (isotropicEnergyValue 2 U x)).re =
      φ x * ‖isotropicEnergyValue 2 U x‖) :
    inner ℝ φ (poissonNormDefectL2 ht (isotropicEnergyValue 2 U)) ≤
      (inner ℂ W (poissonDifferenceQuotient t U)).re := by
  have hire := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner W (poissonDifferenceQuotient t U))
  simp only [Complex.reCLM_apply] at hire
  rw [L2.inner_def, L2.inner_def, ← hire]
  apply integral_mono_ae (L2.integrable_inner φ _)
    (Complex.reCLM.integrable_comp (L2.integrable_inner W (poissonDifferenceQuotient t U)))
  filter_upwards [hw, hs, poissonNormDefectL2_ae ht (isotropicEnergyValue 2 U),
    poissonDifferenceQuotient_ae ht U,
    ae_integrable_poisson_translates ht (isotropicEnergyValue 2 U)]
    with x hwx hsx hnorm hQ hint
  have hp := poisson_weighted_norm_defect_le (isotropicEnergyValue 2 U) x hint hwx hsx
  have hscaled := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr ht.le)
  rw [hnorm, hQ]
  rw [Complex.reCLM_apply, Real.inner_apply, inner_smul_right, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  convert hscaled using 1
  ring

/-- The genuine generator limit passes every lower bound for the actual Kato norm tests. -/
theorem poisson_generator_kato_test_bound (U : H¹) (φ : L²ℝ) (W : L²)
    (hw : ∀ᵐ x, ‖W x‖ ≤ φ x)
    (hs : ∀ᵐ x, (inner ℂ (W x) (isotropicEnergyValue 2 U x)).re =
      φ x * ‖isotropicEnergyValue 2 U x‖) {b : ℝ}
    (hb : ∀ᶠ t in 𝓝[>] 0, ∀ ht : 0 < t,
      b ≤ inner ℝ φ (poissonNormDefectL2 ht (isotropicEnergyValue 2 U))) :
    b ≤ (inner ℂ W (poissonGenerator U)).re := by
  apply ge_of_tendsto (tendsto_poissonGenerator_inner_test U W)
  filter_upwards [hb, self_mem_nhdsWithin] with t ht hpos
  exact (ht hpos).trans (poisson_kato_L2_test hpos U φ W hw hs)

end PartialBalayage.Linear
