/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonQuadraticSpectral
public import PartialBalayage.Linear.PoissonKatoWeak

/-!
# Genuine isotropic energy contraction under the pointwise norm

Actual positive Poisson averaging contracts its quadratic defects under the norm map.
Their universal spectral limit proves contraction of the genuine isotropic half-order
energy, without assuming that the norm already belongs to the energy space.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance poissonNormEnergyRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonNormEnergyScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)

omit [CompleteSpace E] in
/-- Every actual `L²` Poisson quotient has its ordinary spatial representative. -/
theorem poissonQuotientL2_ae {t : ℝ} (ht : 0 < t) (f : L²) :
    ∀ᵐ x, poissonQuotientL2 ht f x =
      (t⁻¹ : ℂ) • (f x - poissonConvolution t f x) := by
  filter_upwards [Lp.coeFn_smul (t⁻¹ : ℂ) (f - poissonConvolutionL2 ht f),
    Lp.coeFn_sub f (poissonConvolutionL2 ht f), poissonConvolutionL2_ae ht f]
    with x hs hd hP
  change ((t⁻¹ : ℂ) • (f - poissonConvolutionL2 ht f)) x = _
  rw [hs, Pi.smul_apply, hd, Pi.sub_apply, hP]

/-- Positive-height Kato holds on every `L²` input, with no generator-domain hypothesis. -/
theorem poisson_kato_L2_input {t : ℝ} (ht : 0 < t) (f : L²) (φ : L²ℝ) (W : L²)
    (hw : ∀ᵐ x, ‖W x‖ ≤ φ x)
    (hs : ∀ᵐ x, (inner ℂ (W x) (f x)).re = φ x * ‖f x‖) :
    inner ℝ φ (poissonNormDefectL2 ht f) ≤ (inner ℂ W (poissonQuotientL2 ht f)).re := by
  have hire := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner W (poissonQuotientL2 ht f))
  simp only [Complex.reCLM_apply] at hire
  rw [L2.inner_def, L2.inner_def, ← hire]
  apply integral_mono_ae (L2.integrable_inner φ _)
    (Complex.reCLM.integrable_comp (L2.integrable_inner W (poissonQuotientL2 ht f)))
  filter_upwards [hw, hs, poissonNormDefectL2_ae ht f,
    poissonQuotientL2_ae ht f, ae_integrable_poisson_translates ht f]
    with x hwx hsx hnorm hQ hint
  have hp := poisson_weighted_norm_defect_le f x hint hwx hsx
  have hscaled := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr ht.le)
  rw [hnorm, hQ]
  rw [Complex.reCLM_apply, Real.inner_apply, inner_smul_right, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  convert hscaled using 1
  ring

/-- Genuine Poisson quadratic defects contract under the actual pointwise norm map. -/
theorem poissonQuadraticDefect_norm_le {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonQuadraticDefect ht (Complex.ofRealCLM.compLp (poissonNormL2 f)) ≤
      poissonQuadraticDefect ht f := by
  have hw : ∀ᵐ x, ‖f x‖ ≤ poissonNormL2 f x := by
    filter_upwards [poissonNormL2_ae f] with x hx
    exact hx.symm.le
  have hs : ∀ᵐ x, (inner ℂ (f x) (f x)).re = poissonNormL2 f x * ‖f x‖ := by
    filter_upwards [poissonNormL2_ae f] with x hx
    rw [hx]
    exact inner_self_eq_norm_mul_norm (𝕜 := ℂ) (f x)
  have h := poisson_kato_L2_input ht f (poissonNormL2 f) f hw hs
  change _ ≤ (inner ℂ f (poissonQuotientL2 ht f)).re
  rw [poissonQuadraticDefect, poissonQuotientL2_complexify, re_inner_complexifyL2]
  exact h

/-- The genuine full isotropic half-order energy contracts under the pointwise norm. -/
theorem fourierEnergy_poissonNormL2_le (f : L²) :
    fourierEnergy 1 (Complex.ofRealCLM.compLp (poissonNormL2 f)) ≤ fourierEnergy 1 f := by
  have h : ENNReal.ofReal (2 * Real.pi) *
      fourierEnergy 1 (Complex.ofRealCLM.compLp (poissonNormL2 f)) ≤
      ENNReal.ofReal (2 * Real.pi) * fourierEnergy 1 f := by
    apply le_of_tendsto_of_tendsto
      (tendsto_poissonQuadraticSpectral (Complex.ofRealCLM.compLp (poissonNormL2 f)))
      (tendsto_poissonQuadraticSpectral f)
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [poissonQuadraticSpectral_eq_ofReal ht, poissonQuadraticSpectral_eq_ofReal ht]
    exact ENNReal.ofReal_le_ofReal (poissonQuadraticDefect_norm_le ht f)
  have hc : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by positivity
  have hcancel := mul_le_mul' (le_refl (ENNReal.ofReal (2 * Real.pi))⁻¹) h
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_mul]
    using hcancel

end PartialBalayage.Linear
