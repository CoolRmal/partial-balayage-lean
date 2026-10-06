/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierSobolevGraph
public import PartialBalayage.Linear.SobolevUnivDensity
public import PartialBalayage.Linear.SobolevZeroSet

/-!
# Zero-set locality of actual represented complex gradients

An actual complex L² value and its represented distributional first derivatives give genuine
real weak-gradient graphs for the value and its multiplication by `I`. Whole-space density
places both graphs in the compact-test closure. Real zero-set locality therefore applies to
both real and imaginary parts of every derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set LineDeriv
open CenteredMaximal.Ball.DirichletSobolev
open scoped SchwartzMap LineDeriv

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)

private theorem ae_real_gradient_zero_aux (u : L²ℂ) (g : Fin n → L²ℂ)
    (hder : ∀ i : Fin n,
      ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(D, ℂ)) = (g i : 𝓢'(D, ℂ))) :
    ∀ᵐ x, (u x : ℂ).re = 0 → ∀ i : Fin n, (g i x : ℂ).re = 0 := by
  let U : H01 (univ : Set D) := ⟨complexL2GradientGraph u g,
    mem_H01_univ_of_mem_W12 (complexL2GradientGraph_mem_W12 u g hder)⟩
  have hzero : ∀ᵐ x, (complexL2GradientGraph u g 0 x : ℝ) = 0 →
      ∀ i : Fin n, (complexL2GradientGraph u g i.succ x : ℝ) = 0 := by
    simpa only [Measure.restrict_univ] using
      ae_all_gradients_eq_zero_on_value_zero isOpen_univ U
  have hgrad := ae_all_iff.mpr (complexL2GradientGraph_partial_ae u g)
  filter_upwards [hzero, complexL2GradientGraph_value_ae u g, hgrad] with x hz hv hg
  intro hu i
  rw [← hg i]
  exact hz (hv.trans hu) i

/-- Every actual represented complex derivative vanishes on the actual value zero set. -/
theorem ae_complex_gradient_eq_zero_on_value_zero (u : L²ℂ) (g : Fin n → L²ℂ)
    (hder : ∀ i : Fin n,
      ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(D, ℂ)) = (g i : 𝓢'(D, ℂ))) :
    ∀ᵐ x, u x = 0 → ∀ i : Fin n, g i x = 0 := by
  have hderI : ∀ i : Fin n,
      ∂_{EuclideanSpace.single i (1 : ℝ)} ((Complex.I • u : L²ℂ) : 𝓢'(D, ℂ)) =
        ((Complex.I • g i : L²ℂ) : 𝓢'(D, ℂ)) := by
    intro i
    change ∂_{EuclideanSpace.single i (1 : ℝ)}
      (Lp.toTemperedDistributionCLM ℂ volume 2 (Complex.I • u)) =
        Lp.toTemperedDistributionCLM ℂ volume 2 (Complex.I • g i)
    rw [map_smul, lineDerivOp_smul, map_smul]
    simp only [Lp.toTemperedDistributionCLM_apply, hder i]
  have hRe := ae_real_gradient_zero_aux u g hder
  have hIm := ae_real_gradient_zero_aux (Complex.I • u) (fun i ↦ Complex.I • g i) hderI
  have hgI := ae_all_iff.mpr (fun i : Fin n ↦ Lp.coeFn_smul Complex.I (g i))
  filter_upwards [hRe, hIm, Lp.coeFn_smul Complex.I u, hgI] with x hre him hu hg
  intro hzero i
  have hreal : (g i x : ℂ).re = 0 := hre (by simp only [hzero, Complex.zero_re]) i
  have himag : (g i x : ℂ).im = 0 := by
    have he := him (by rw [hu]; simp [hzero]) i
    rw [hg i, Pi.smul_apply, smul_eq_mul] at he
    simpa using he
  exact Complex.ext hreal himag

end PartialBalayage.Linear
