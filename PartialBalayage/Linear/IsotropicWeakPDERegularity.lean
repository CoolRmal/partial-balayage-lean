/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonWeakRegularization

/-!
# Actual first-order regularity from the half-order weak equation

The nonvanishing spatial Poisson multiplier cancels from the true regularized
equation. The actual right-hand side supplies the full norm-weighted L2 Fourier
coordinate, constructing a genuine first-order state with the original value.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "WholeState" => IsotropicDirichletState (univ : Set D)

/-- The true weak equation gives the actual full-norm Fourier identity. -/
theorem isotropicWeakPDE_norm_fourier_ae (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ V : WholeState, isotropicDirichletForm univ U V =
      inner ℝ q (isotropicDirichletGlobalValue univ V)) :
    ∀ᵐ ξ, (‖ξ‖ : ℂ) • (𝓕 (isotropicEnergyValue 1 U.val) : L²ℂ) ξ =
      (2 * Real.pi : ℂ)⁻¹ • (𝓕 (Complex.ofRealCLM.compLp q) : L²ℂ) ξ := by
  have ht : (0 : ℝ) < 1 := by norm_num
  have h := poissonGenerator_regularized_weakPDE ht U q hPDE
  rw [← poissonConvolutionL2_compLp ht] at h
  have hF := congrArg (fun f : L²ℂ ↦ 𝓕 f) h
  have hQ : ∀ᵐ ξ, (𝓕 (poissonConvolutionL2 ht (Complex.ofRealCLM.compLp q)) : L²ℂ) ξ =
      (poissonOperatorSymbol 1 ξ) ((𝓕 (Complex.ofRealCLM.compLp q) : L²ℂ) ξ) := by
    rw [fourier_poissonConvolutionL2 ht]
    exact multiplyOperatorL2_ae (poissonOperatorSymbol 1)
      (aestronglyMeasurable_poissonOperatorSymbol 1) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 (Complex.ofRealCLM.compLp q))
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
  filter_upwards [Lp.ext_iff.mp hF,
    fourier_poissonSmoothedGenerator_ae ht (isotropicEnergyValue 1 U.val), hQ]
    with ξ he hg hq
  rw [hg, hq] at he
  simp only [poissonOperatorSymbol, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul] at he
  have ha : (Real.exp (-(2 * Real.pi * 1 * ‖ξ‖)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hm : (2 * Real.pi : ℂ) *
      ((‖ξ‖ : ℂ) * (𝓕 (isotropicEnergyValue 1 U.val) : L²ℂ) ξ) =
      (𝓕 (Complex.ofRealCLM.compLp q) : L²ℂ) ξ := by
    apply mul_left_cancel₀ ha
    calc
      _ = ((2 * Real.pi * ‖ξ‖ * Real.exp (-(2 * Real.pi * 1 * ‖ξ‖)) : ℝ) : ℂ) *
          (𝓕 (isotropicEnergyValue 1 U.val) : L²ℂ) ξ := by push_cast; ring
      _ = _ := he
  change (‖ξ‖ : ℂ) * (𝓕 (isotropicEnergyValue 1 U.val) : L²ℂ) ξ =
    (2 * Real.pi : ℂ)⁻¹ * (𝓕 (Complex.ofRealCLM.compLp q) : L²ℂ) ξ
  apply mul_left_cancel₀ hπ
  rw [mul_inv_cancel_left₀ hπ]
  exact hm

/-- The actual first-order state obtained from the genuine half-order weak equation. -/
def isotropicWeakPDEStateTwo (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ V : WholeState, isotropicDirichletForm univ U V =
      inner ℝ q (isotropicDirichletGlobalValue univ V)) :
    IsotropicEnergySpace (X := D) (E := ℂ) 2 :=
  ⟨WithLp.toLp 2 (Fin.cons (isotropicEnergyValue 1 U.val)
    (fun _ : Fin 1 ↦ (2 * Real.pi : ℂ)⁻¹ • 𝓕 (Complex.ofRealCLM.compLp q))), by
      change ∀ᵐ ξ, ((2 * Real.pi : ℂ)⁻¹ • 𝓕 (Complex.ofRealCLM.compLp q) : L²ℂ) ξ =
        ((‖ξ‖ ^ ((2 : ℝ) / 2) : ℝ) : ℂ) •
          (𝓕 (isotropicEnergyValue 1 U.val) : L²ℂ) ξ
      filter_upwards [isotropicWeakPDE_norm_fourier_ae U q hPDE,
        Lp.coeFn_smul (2 * Real.pi : ℂ)⁻¹ (𝓕 (Complex.ofRealCLM.compLp q))]
        with ξ he hs
      rw [hs, Pi.smul_apply]
      rw [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
      exact he.symm⟩

/-- The regularity construction preserves the genuine original physical value. -/
theorem isotropicEnergyValue_isotropicWeakPDEStateTwo (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ V : WholeState, isotropicDirichletForm univ U V =
      inner ℝ q (isotropicDirichletGlobalValue univ V)) :
    isotropicEnergyValue 2 (isotropicWeakPDEStateTwo U q hPDE) =
      isotropicEnergyValue 1 U.val := rfl

end PartialBalayage.Linear
