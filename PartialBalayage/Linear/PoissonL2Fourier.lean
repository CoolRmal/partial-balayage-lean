/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonL2

/-!
# Fourier identification of actual Poisson `L²` averaging

The normalized spatial probability average equals the genuine unitary Fourier multiplier
with symbol `exp (-2 * π * t * ‖ξ‖)`. Identification first uses ordinary convolution on
integrable `L²` inputs, and then passes to every `L²` input by Schwartz density.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set Filter ContinuousLinearMap
open scoped ENNReal Convolution RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure X)

/-- The actual isotropic scalar Poisson symbol as an operator on a complex Hilbert output. -/
def poissonOperatorSymbol (t : ℝ) (ξ : X) : E →L[ℂ] E :=
  (Real.exp (-(2 * Real.pi * t * ‖ξ‖)) : ℂ) • ContinuousLinearMap.id ℂ E

omit [CompleteSpace E] in
/-- The actual Poisson operator symbol is strongly measurable. -/
theorem aestronglyMeasurable_poissonOperatorSymbol (t : ℝ) :
    AEStronglyMeasurable (poissonOperatorSymbol (n := n) (E := E) t) volume := by
  have hcont : Continuous (poissonOperatorSymbol (n := n) (E := E) t) := by
    unfold poissonOperatorSymbol
    fun_prop
  exact hcont.aestronglyMeasurable

omit [CompleteSpace E] in
/-- The exact positive-height Poisson symbol has operator norm at most one. -/
theorem norm_poissonOperatorSymbol_le {t : ℝ} (ht : 0 ≤ t) (ξ : X) :
    ‖poissonOperatorSymbol (E := E) t ξ‖ ≤ 1 := by
  rw [poissonOperatorSymbol, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(2 * Real.pi * t * ‖ξ‖)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg (mul_nonneg (by positivity) ht) (norm_nonneg ξ)))
  exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
    (Real.exp_pos _).le).trans (by simpa only [mul_one] using he)

/-- The genuine complex-linear Poisson Fourier multiplier on the actual Hilbert `L²` space. -/
def poissonFourierL2CLM {t : ℝ} (ht : 0 ≤ t) : L² →L[ℂ] L² :=
  operatorMultiplierL2CLM (poissonOperatorSymbol t)
    (aestronglyMeasurable_poissonOperatorSymbol t) 1 (norm_poissonOperatorSymbol_le ht)

omit [CompleteSpace E] in
/-- The actual probability average agrees with ordinary complex scalar convolution. -/
theorem poissonConvolution_eq_complex_convolution {t : ℝ} (ht : 0 < t) (f : X → E) :
    poissonConvolution t f =
      (fun y : X ↦ (PartialBalayage.poissonKernel n t y : ℂ)) ⋆[lsmul ℂ ℂ] f := by
  funext x
  unfold poissonConvolution PartialBalayage.poissonKernelMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (by unfold PartialBalayage.poissonKernel; fun_prop)
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [ENNReal.toReal_ofReal (PartialBalayage.poissonKernel_pos n ht y).le,
    lsmul_apply, Complex.coe_smul]

omit [CompleteSpace E] in
/-- Integrable `L²` inputs give genuinely integrable spatial Poisson output representatives. -/
theorem integrable_poissonConvolutionL2 {t : ℝ} (ht : 0 < t) (f : L²)
    (hf : Integrable (f : X → E)) : Integrable (poissonConvolutionL2 ht f : X → E) := by
  have hK : Integrable (fun y : X ↦ (PartialBalayage.poissonKernel n t y : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (PartialBalayage.integrable_poissonKernel n ht)
  have hconv := hK.integrable_convolution (lsmul ℂ ℂ) hf
  apply hconv.congr
  exact ((poissonConvolutionL2_ae ht f).trans
    (EventuallyEq.of_eq (poissonConvolution_eq_complex_convolution ht f))).symm

/-- Ordinary Fourier convolution identifies the genuine `L²` output on integrable inputs. -/
theorem fourier_poissonConvolutionL2_of_integrable {t : ℝ} (ht : 0 < t) (f : L²)
    (hf : Integrable (f : X → E)) :
    𝓕 (poissonConvolutionL2 ht f) = multiplyOperatorL2 (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f) := by
  have hK : Integrable (fun y : X ↦ (PartialBalayage.poissonKernel n t y : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (PartialBalayage.integrable_poissonKernel n ht)
  have hsource := (poissonConvolutionL2_ae ht f).trans
    (EventuallyEq.of_eq (poissonConvolution_eq_complex_convolution ht f))
  apply Lp.ext
  filter_upwards [fourier_L2_ae_eq_integral (poissonConvolutionL2 ht f)
    (integrable_poissonConvolutionL2 ht f hf), fourier_L2_ae_eq_integral f hf,
    multiplyOperatorL2_ae (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f)] with ξ hP hfξ hmult
  rw [hP, Real.fourier_congr_ae hsource ξ,
    Real.fourier_smul_convolution_eq hK hf, fourier_poissonKernel ht ξ, hmult, hfξ]
  rfl

/-- Schwartz density identifies genuine spatial Poisson averaging on every Hilbert `L²` input. -/
theorem fourier_poissonConvolutionL2 {t : ℝ} (ht : 0 < t) (f : L²) :
    𝓕 (poissonConvolutionL2 ht f) = multiplyOperatorL2 (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f) := by
  apply DenseRange.induction_on
    (p := fun g : L² ↦ 𝓕 (poissonConvolutionL2 ht g) =
      multiplyOperatorL2 (poissonOperatorSymbol t)
        (aestronglyMeasurable_poissonOperatorSymbol t) 1
        (norm_poissonOperatorSymbol_le ht.le) (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ X E).continuous.comp (poissonConvolutionL2CLM ht).continuous)
      ((multiplyOperatorL2CLM (poissonOperatorSymbol t)
        (aestronglyMeasurable_poissonOperatorSymbol t) 1
        (norm_poissonOperatorSymbol_le ht.le)).continuous.comp
          (Lp.fourierTransformₗᵢ X E).continuous)
  intro φ
  apply fourier_poissonConvolutionL2_of_integrable ht
  exact φ.integrable.congr (φ.coeFn_toLp 2).symm

/-- The actual spatial Poisson `L²` operator equals its genuine isotropic Fourier multiplier. -/
theorem poissonConvolutionL2_eq_fourier {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonConvolutionL2 ht f = poissonFourierL2CLM ht.le f := by
  apply (Lp.fourierTransformₗᵢ X E).injective
  change 𝓕 (poissonConvolutionL2 ht f) = 𝓕 (poissonFourierL2CLM ht.le f)
  rw [fourier_poissonConvolutionL2 ht f]
  exact (fourier_operatorMultiplierL2CLM (poissonOperatorSymbol t)
    (aestronglyMeasurable_poissonOperatorSymbol t) 1
    (norm_poissonOperatorSymbol_le ht.le) f).symm

end PartialBalayage.Linear
