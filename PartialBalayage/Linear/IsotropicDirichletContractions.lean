/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.IsotropicDirichletSpace
public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Actual scalar normal contractions on the isotropic Dirichlet space

A scalar one-Lipschitz map fixing zero acts on genuine real half-order states. Positive
Poisson increments prove the energy contraction, and the actual exterior support is
preserved. These states provide the signed monotone tests for the dual obstacle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)

/-- The complex-valued lift of an actual real scalar contraction. -/
def isotropicScalarLift (η : ℝ → ℝ) (z : ℂ) : ℂ := η z.re

/-- Real projection and isometric complexification preserve a one-Lipschitz bound. -/
theorem lipschitz_isotropicScalarLift (η : ℝ → ℝ) (hη : LipschitzWith 1 η) :
    LipschitzWith 1 (isotropicScalarLift η) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  simp only [isotropicScalarLift, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have h := hη.norm_sub_le z.re w.re
  simp only [NNReal.coe_one, one_mul, Real.norm_eq_abs] at h
  exact h.trans (Complex.abs_re_le_norm (z - w))

theorem isotropicScalarLift_zero (η : ℝ → ℝ) (h₀ : η 0 = 0) :
    isotropicScalarLift η 0 = 0 := by simp [isotropicScalarLift, h₀]

/-- Actual scalar contractions preserve reality and exterior zero values in the energy graph. -/
theorem isotropicScalarContraction_mem_supported {Ω : Set D} (hΩ : MeasurableSet Ω)
    (η : ℝ → ℝ) (hη : LipschitzWith 1 η) (h₀ : η 0 = 0)
    {U : IsotropicScalarEnergy (n := n) 1} (hU : U ∈ isotropicRealSupported Ω) :
    isotropicMarkovStateOne (isotropicScalarLift η) (lipschitz_isotropicScalarLift η hη)
      (isotropicScalarLift_zero η h₀) U ∈ isotropicRealSupported Ω := by
  rw [mem_isotropicRealSupported_iff hΩ] at hU ⊢
  have he := poissonMarkovL2_ae (isotropicScalarLift η)
    (lipschitz_isotropicScalarLift η hη) (isotropicScalarLift_zero η h₀)
    (isotropicEnergyValue 1 U)
  rw [isotropicEnergyValue_isotropicMarkovStateOne]
  constructor
  · filter_upwards [he] with x hx
    rw [hx, isotropicScalarLift, Complex.ofReal_im]
  · filter_upwards [he, hU.2] with x hx hs
    intro hxo
    rw [hx, hs hxo, isotropicScalarLift_zero η h₀]

/-- The genuine real zero-exterior normal-contraction state. -/
def isotropicDirichletContraction {Ω : Set D} (hΩ : MeasurableSet Ω)
    (η : ℝ → ℝ) (hη : LipschitzWith 1 η) (h₀ : η 0 = 0)
    (U : IsotropicDirichletState Ω) : IsotropicDirichletState Ω :=
  ⟨isotropicMarkovStateOne (isotropicScalarLift η) (lipschitz_isotropicScalarLift η hη)
    (isotropicScalarLift_zero η h₀) U.val,
    isotropicScalarContraction_mem_supported hΩ η hη h₀ U.property⟩

/-- The actual physical value is the scalar composition of the original state value. -/
theorem isotropicDirichletContraction_value_ae {Ω : Set D} (hΩ : MeasurableSet Ω)
    (η : ℝ → ℝ) (hη : LipschitzWith 1 η) (h₀ : η 0 = 0)
    (U : IsotropicDirichletState Ω) :
    isotropicDirichletGlobalValue Ω (isotropicDirichletContraction hΩ η hη h₀ U) =ᵐ[volume]
      fun x ↦ η (isotropicDirichletGlobalValue Ω U x) := by
  have he := poissonMarkovL2_ae (isotropicScalarLift η)
    (lipschitz_isotropicScalarLift η hη) (isotropicScalarLift_zero η h₀)
    (isotropicEnergyValue 1 U.val)
  filter_upwards [he, isotropicDirichletGlobalValue_ae U,
    isotropicDirichletGlobalValue_ae (isotropicDirichletContraction hΩ η hη h₀ U)]
    with x hmark hU hηU
  have hv : isotropicEnergyValue 1
      (isotropicDirichletContraction hΩ η hη h₀ U).val =
      poissonMarkovL2 (isotropicScalarLift η) (lipschitz_isotropicScalarLift η hη)
        (isotropicScalarLift_zero η h₀) (isotropicEnergyValue 1 U.val) := rfl
  rw [hv, hmark, isotropicScalarLift, Complex.ofReal_re, ← hU] at hηU
  exact hηU

/-- The true isotropic half-order energy contracts under actual scalar normal contractions. -/
theorem isotropicDirichletContraction_energy_le {Ω : Set D} (hΩ : MeasurableSet Ω)
    (η : ℝ → ℝ) (hη : LipschitzWith 1 η) (h₀ : η 0 = 0)
    (U : IsotropicDirichletState Ω) :
    ‖isotropicDirichletData Ω (isotropicDirichletContraction hΩ η hη h₀ U)‖ ^ 2 ≤
      ‖isotropicDirichletData Ω U‖ ^ 2 := by
  have h := isotropicEnergyData_markovStateOne_le (isotropicScalarLift η)
    (lipschitz_isotropicScalarLift η hη) (isotropicScalarLift_zero η h₀) U.val
  have ht := ENNReal.toReal_mono (ENNReal.pow_ne_top enorm_ne_top) h
  change ‖isotropicEnergyData 1 (isotropicMarkovStateOne (isotropicScalarLift η)
    (lipschitz_isotropicScalarLift η hη) (isotropicScalarLift_zero η h₀) U.val)‖ ^ 2 ≤
      ‖isotropicEnergyData 1 U.val‖ ^ 2
  simpa only [← ofReal_norm, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (norm_nonneg _)] using ht

end PartialBalayage.Linear
