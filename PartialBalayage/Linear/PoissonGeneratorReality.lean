/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonKatoWeak
public import PartialBalayage.Linear.IsotropicEnergyPairing

/-!
# The actual Poisson generator preserves real-valuedness

Strong convergence of the genuine spatial difference quotients preserves the
closed real-valued L2 subspace. No Fourier reality condition is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := ℂ) 2

/-- An actual complexified real L2 class has zero imaginary observation. -/
theorem im_compLp_complexify_eq_zero (f : L²ℝ) :
    Complex.imCLM.compLp (Complex.ofRealCLM.compLp f) = 0 := by
  apply Lp.ext
  filter_upwards [Complex.imCLM.coeFn_compLp (Complex.ofRealCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp f,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure D))] with x hi hr hz
  rw [hi, hr, hz]
  simp only [Pi.zero_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply,
    Complex.ofReal_im]

/-- The true generator of a real-valued first-order state has zero imaginary part. -/
theorem im_compLp_poissonGenerator_eq_zero (U : H¹) (f : L²ℝ)
    (hU : isotropicEnergyValue 2 U = Complex.ofRealCLM.compLp f) :
    Complex.imCLM.compLp (poissonGenerator U) = 0 := by
  have hlim := ((Complex.imCLM.compLpL 2 (volume : Measure D)).continuous.tendsto
    (poissonGenerator U)).comp (tendsto_poissonDifferenceQuotient U)
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Complex.imCLM.compLp (poissonDifferenceQuotient t U) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Ioi] at ht
    rw [poissonDifferenceQuotient, dite_eq_left ht]
    change Complex.imCLM.compLp (poissonQuotientL2 ht (isotropicEnergyValue 2 U)) = 0
    rw [hU, poissonQuotientL2_complexify ht]
    exact im_compLp_complexify_eq_zero _
  have hzero : Tendsto (fun t ↦ Complex.imCLM.compLp (poissonDifferenceQuotient t U))
      (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' (he.mono fun _ ht ↦ ht.symm)
  exact tendsto_nhds_unique hlim hzero

/-- Zero imaginary observation identifies the actual complex class with its real part. -/
theorem complexify_re_compLp_of_im_eq_zero (f : L²ℂ)
    (hf : Complex.imCLM.compLp f = 0) :
    Complex.ofRealCLM.compLp (Complex.reCLM.compLp f) = f := by
  have him := (Lp.eq_zero_iff_ae_eq_zero).mp hf
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (Complex.reCLM.compLp f),
    Complex.reCLM.coeFn_compLp f, Complex.imCLM.coeFn_compLp f, him]
    with x hc hr hi hz
  rw [hc, hr]
  have hix : (f x).im = 0 := by
    simpa only [Complex.imCLM_apply, Pi.zero_apply] using hi.symm.trans hz
  apply Complex.ext
  · simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.ofReal_re]
  · simpa only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.ofReal_im] using
      hix.symm

end PartialBalayage.Linear
