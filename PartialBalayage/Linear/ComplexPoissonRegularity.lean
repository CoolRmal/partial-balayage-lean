/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonH01TestClosure
public import PartialBalayage.Linear.IsotropicWeakPDERegularity

/-!
# Genuine complex Poisson regularity from the physical weak equation

Complexified real tests determine every complex Hilbert-space pairing. Actual
Poisson smoothing therefore identifies the full complex regularized generator,
and its nonvanishing multiplier gives the genuine full frequency-norm identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)

/-- Every genuine complex L² class is the sum of its real and imaginary classes. -/
theorem complexLp_real_imaginary_decomposition (f : L²ℂ) :
    f = Complex.ofRealCLM.compLp (Complex.reCLM.compLp f) +
      Complex.I • Complex.ofRealCLM.compLp (Complex.imCLM.compLp f) := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp f, Complex.imCLM.coeFn_compLp f,
    Complex.ofRealCLM.coeFn_compLp (Complex.reCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp (Complex.imCLM.compLp f),
    Lp.coeFn_add (Complex.ofRealCLM.compLp (Complex.reCLM.compLp f))
      (Complex.I • Complex.ofRealCLM.compLp (Complex.imCLM.compLp f)),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLp (Complex.imCLM.compLp f))]
    with x hr hi hrr hii ha hs
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hrr, hii, hr, hi]
  change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (f x)).symm

/-- Agreement on all complexified real tests determines a genuine complex L² class. -/
theorem complexLp_eq_of_inner_real_tests {u v : L²ℂ}
    (h : ∀ f : L²ℝ, inner ℂ u (Complex.ofRealCLM.compLp f) =
      inner ℂ v (Complex.ofRealCLM.compLp f)) : u = v := by
  apply ext_inner_right ℂ
  intro g
  rw [complexLp_real_imaginary_decomposition g]
  simp only [inner_add_right, inner_smul_right]
  rw [h, h]

/-- The true complex physical equation identifies the actual regularized generator. -/
theorem complex_poissonGenerator_regularized_of_h01_equation {t : ℝ} (ht : 0 < t)
    (u q : L²ℂ)
    (hPDE : ∀ W : H01 (univ : Set D),
      inner ℂ u (h01PoissonGenerator W) = inner ℂ q (h01ComplexValueCLM W)) :
    poissonGenerator (poissonSmoothedStateTwo ht u) = poissonConvolutionL2 ht q := by
  apply complexLp_eq_of_inner_real_tests
  intro f
  let V := poissonSmoothedStateTwo ht (Complex.ofRealCLM.compLp f)
  have hv : isotropicEnergyValue 2 V =
      Complex.ofRealCLM.compLp (poissonConvolutionL2 ht f) := by
    rw [isotropicEnergyValue_poissonSmoothedStateTwo, poissonConvolutionL2_compLp ht]
  have hw : h01ComplexValueCLM (isotropicTwoH01 V) =
      Complex.ofRealCLM.compLp (poissonConvolutionL2 ht f) := by
    rw [h01ComplexValueCLM_eq_complexify, h01RealValueCLM_isotropicTwoH01 V _ hv]
  have h := hPDE (isotropicTwoH01 V)
  rw [h01PoissonGenerator_isotropicTwoH01 V _ hv, hw] at h
  rw [← inner_poissonSmoothedGenerator ht u (Complex.ofRealCLM.compLp f)]
  have hs := inner_poissonConvolutionL2 ht q (Complex.ofRealCLM.compLp f)
  rw [poissonConvolutionL2_compLp ht] at hs
  exact h.trans hs

/-- An actual regularized equation gives the genuine full frequency-norm identity. -/
theorem complex_isotropicNormFourier_ae_of_regularizedEquation (f : L²ℂ) (q : L²ℂ)
    (hEquation : poissonGenerator (poissonSmoothedStateTwo (by norm_num : (0 : ℝ) < 1) f) =
      poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) q) :
    ∀ᵐ ξ, (‖ξ‖ : ℂ) • (𝓕 f : L²ℂ) ξ =
      (2 * Real.pi : ℂ)⁻¹ • (𝓕 q : L²ℂ) ξ := by
  have ht : (0 : ℝ) < 1 := by norm_num
  have h := hEquation
  have hF := congrArg (fun f : L²ℂ ↦ 𝓕 f) h
  have hQ : ∀ᵐ ξ, (𝓕 (poissonConvolutionL2 ht q) : L²ℂ) ξ =
      (poissonOperatorSymbol 1 ξ) ((𝓕 q : L²ℂ) ξ) := by
    rw [fourier_poissonConvolutionL2 ht]
    exact multiplyOperatorL2_ae (poissonOperatorSymbol 1)
      (aestronglyMeasurable_poissonOperatorSymbol 1) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 q)
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
  filter_upwards [Lp.ext_iff.mp hF,
    fourier_poissonSmoothedGenerator_ae ht (f), hQ]
    with ξ he hg hq
  rw [hg, hq] at he
  simp only [poissonOperatorSymbol, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul] at he
  have ha : (Real.exp (-(2 * Real.pi * 1 * ‖ξ‖)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hm : (2 * Real.pi : ℂ) *
      ((‖ξ‖ : ℂ) * (𝓕 (f) : L²ℂ) ξ) =
      (𝓕 q : L²ℂ) ξ := by
    apply mul_left_cancel₀ ha
    calc
      _ = ((2 * Real.pi * ‖ξ‖ * Real.exp (-(2 * Real.pi * 1 * ‖ξ‖)) : ℝ) : ℂ) *
          (𝓕 (f) : L²ℂ) ξ := by push_cast; ring
      _ = _ := he
  change (‖ξ‖ : ℂ) * (𝓕 (f) : L²ℂ) ξ =
    (2 * Real.pi : ℂ)⁻¹ * (𝓕 q : L²ℂ) ξ
  apply mul_left_cancel₀ hπ
  rw [mul_inv_cancel_left₀ hπ]
  exact hm

/-- The actual complex physical equation yields the full norm-weighted Fourier identity. -/
theorem complex_isotropicNormFourier_ae_of_h01_equation (u q : L²ℂ)
    (hPDE : ∀ W : H01 (univ : Set D),
      inner ℂ u (h01PoissonGenerator W) = inner ℂ q (h01ComplexValueCLM W)) :
    ∀ᵐ ξ, (‖ξ‖ : ℂ) • (𝓕 u : L²ℂ) ξ =
      (2 * Real.pi : ℂ)⁻¹ • (𝓕 q : L²ℂ) ξ :=
  complex_isotropicNormFourier_ae_of_regularizedEquation u q
    (complex_poissonGenerator_regularized_of_h01_equation (by norm_num) u q hPDE)

end PartialBalayage.Linear
