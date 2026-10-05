/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.IsotropicWeakPDERegularity

/-!
# Actual Poisson tests imply the complete half-order weak equation

The height-one Poisson tests recover genuine first-order regularity with
the original physical value. Their actual generator is the original data.
The exact generator/form pairing then proves the weak equation against every
half-order state, including the state itself for the true energy identity.
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

/-- The actual physical value uniquely determines its true weighted Fourier data. -/
theorem isotropicEnergyData_eq_of_value_eq (α : ℝ)
    (U V : IsotropicEnergySpace (X := D) (E := ℂ) α)
    (hValue : isotropicEnergyValue α U = isotropicEnergyValue α V) :
    isotropicEnergyData α U = isotropicEnergyData α V := by
  apply Lp.ext
  filter_upwards [U.property, V.property] with ξ hU hV
  change isotropicEnergyData α U ξ =
    ((‖ξ‖ ^ (α / 2) : ℝ) : ℂ) • (𝓕 (isotropicEnergyValue α U) : L²ℂ) ξ at hU
  change isotropicEnergyData α V ξ =
    ((‖ξ‖ ^ (α / 2) : ℝ) : ℂ) • (𝓕 (isotropicEnergyValue α V) : L²ℂ) ξ at hV
  rw [hValue] at hU
  exact hU.trans hV.symm

/-- The actual unregularized generator recovered from the true Poisson tests is its data. -/
theorem poissonGenerator_isotropicPoissonTestStateTwo (U : WholeState) (q : L²ℝ)
    (hTest : ∀ f : L²ℝ, isotropicDirichletForm univ U
      (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) f) =
        inner ℝ q (poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) f)) :
    poissonGenerator (isotropicPoissonTestStateTwo U q hTest) =
      Complex.ofRealCLM.compLp q := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
  change 𝓕⁻ ((2 * Real.pi : ℂ) •
    ((2 * Real.pi : ℂ)⁻¹ • 𝓕 (Complex.ofRealCLM.compLp q))) = _
  rw [smul_smul, mul_inv_cancel₀ hπ, one_smul]
  exact fourierInv_fourier_eq _

/-- The actual height-one Poisson test equations imply every genuine half-order weak test. -/
theorem isotropicWeakPDE_of_Poisson_test_equations (U : WholeState) (q : L²ℝ)
    (hTest : ∀ f : L²ℝ, isotropicDirichletForm univ U
      (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) f) =
        inner ℝ q (poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) f)) :
    ∀ V : WholeState, isotropicDirichletForm univ U V =
      inner ℝ q (isotropicDirichletGlobalValue univ V) := by
  intro V
  let S := isotropicPoissonTestStateTwo U q hTest
  have hd : isotropicEnergyData 1 U.val =
      isotropicEnergyData 1 (isotropicHalfStateOfTwo S) :=
    isotropicEnergyData_eq_of_value_eq 1 U.val (isotropicHalfStateOfTwo S) rfl
  rw [isotropicDirichletForm_apply, real_inner_comm, real_inner_complexLp]
  change 2 * Real.pi * (inner ℂ (isotropicEnergyData 1 V.val)
    (isotropicEnergyData 1 U.val)).re = _
  rw [hd]
  have h := congrArg Complex.re (inner_isotropicHalfDataOfTwo V.val S)
  norm_num [Complex.mul_re, Complex.mul_im] at h
  rw [h]
  change (inner ℂ (isotropicEnergyValue 1 V.val)
    (poissonGenerator (isotropicPoissonTestStateTwo U q hTest))).re = _
  rw [poissonGenerator_isotropicPoissonTestStateTwo,
    isotropicDirichlet_complexValue_eq MeasurableSet.univ V,
    re_inner_complexifyL2, real_inner_comm]

/-- The true limiting state's energy identity follows from its actual Poisson tests. -/
theorem isotropicDirichletForm_self_of_Poisson_test_equations (U : WholeState) (q : L²ℝ)
    (hTest : ∀ f : L²ℝ, isotropicDirichletForm univ U
      (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) f) =
        inner ℝ q (poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) f)) :
    isotropicDirichletForm univ U U = inner ℝ q (isotropicDirichletGlobalValue univ U) :=
  isotropicWeakPDE_of_Poisson_test_equations U q hTest U

end PartialBalayage.Linear
