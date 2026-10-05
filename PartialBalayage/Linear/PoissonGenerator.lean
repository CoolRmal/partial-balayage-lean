/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonL2Fourier
public import PartialBalayage.Linear.PoissonGeneratorScalar
public import PartialBalayage.Linear.L2DominatedLimit
public import PartialBalayage.Linear.IsotropicEnergySpace

/-!
# The actual isotropic Poisson generator

Positive-height difference quotients of the actual normalized Poisson convolution converge
strongly on the genuine isotropic first-order domain. The generator is multiplication by
`2 * π * ‖ξ‖` under the unitary Fourier transform, in every dimension.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := E) 2

/-- The genuine isotropic square-root Laplace generator, with the Fourier normalization. -/
def poissonGenerator (U : H¹) : L² :=
  𝓕⁻ ((2 * Real.pi : ℂ) • isotropicEnergyData 2 U)

/-- The genuine spatial Poisson difference quotient at positive height, extended by zero. -/
def poissonDifferenceQuotient (t : ℝ) (U : H¹) : L² :=
  if ht : 0 < t then (t⁻¹ : ℂ) •
    (isotropicEnergyValue 2 U - poissonConvolutionL2 ht (isotropicEnergyValue 2 U)) else 0

/-- The energy graph represents the actual full frequency norm times the value transform. -/
theorem isotropicEnergyData_two_ae (U : H¹) :
    ∀ᵐ ξ, isotropicEnergyData 2 U ξ =
      (‖ξ‖ : ℂ) • (𝓕 (isotropicEnergyValue 2 U) : L²) ξ := by
  have h := U.property
  change ∀ᵐ ξ, (U.val 1) ξ =
    (((‖ξ‖ ^ ((2 : ℝ) / 2)) : ℝ) : ℂ) • (𝓕 (U.val 0) : L²) ξ at h
  simpa only [isotropicEnergyData_apply, isotropicEnergyValue_apply,
    div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using h

/-- The actual generator's Fourier representative is the full isotropic multiplier. -/
theorem fourier_poissonGenerator_ae (U : H¹) :
    ∀ᵐ ξ, (𝓕 (poissonGenerator U) : L²) ξ =
      ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) • (𝓕 (isotropicEnergyValue 2 U) : L²) ξ := by
  rw [poissonGenerator, fourier_fourierInv_eq]
  filter_upwards [isotropicEnergyData_two_ae U,
    Lp.coeFn_smul (2 * Real.pi : ℂ) (isotropicEnergyData 2 U)] with ξ hg hs
  rw [hs, Pi.smul_apply, hg, smul_smul]
  push_cast
  rfl

/-- Fourier transformation gives the exact scalar quotient of the actual spatial operator. -/
theorem fourier_poissonDifferenceQuotient_ae {t : ℝ} (ht : 0 < t) (U : H¹) :
    ∀ᵐ ξ, (𝓕 (poissonDifferenceQuotient t U) : L²) ξ =
      (poissonRate t (2 * Real.pi * ‖ξ‖) : ℂ) •
        (𝓕 (isotropicEnergyValue 2 U) : L²) ξ := by
  have hsubF (f g : L²) : 𝓕 (f - g) = 𝓕 f - 𝓕 g :=
    (Lp.fourierTransformₗᵢ D E).map_sub f g
  rw [poissonDifferenceQuotient, dite_eq_left ht, fourier_smul, hsubF,
    fourier_poissonConvolutionL2 ht]
  filter_upwards [Lp.coeFn_smul (t⁻¹ : ℂ)
    (𝓕 (isotropicEnergyValue 2 U) - multiplyOperatorL2 (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 (isotropicEnergyValue 2 U))),
    Lp.coeFn_sub (𝓕 (isotropicEnergyValue 2 U))
      (multiplyOperatorL2 (poissonOperatorSymbol t)
        (aestronglyMeasurable_poissonOperatorSymbol t) 1
        (norm_poissonOperatorSymbol_le ht.le) (𝓕 (isotropicEnergyValue 2 U))),
    multiplyOperatorL2_ae (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 (isotropicEnergyValue 2 U))]
    with ξ hs hsub hmult
  rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, hmult]
  change (t⁻¹ : ℂ) • ((𝓕 (isotropicEnergyValue 2 U) : L²) ξ -
    (Real.exp (-(2 * Real.pi * t * ‖ξ‖)) : ℂ) •
      (𝓕 (isotropicEnergyValue 2 U) : L²) ξ) = _
  have hid (c : ℂ) (v : E) : v - c • v = (1 - c) • v := by
    rw [sub_smul, one_smul]
  rw [hid, smul_smul]
  congr 1
  rw [poissonRate, ite_eq_left ht]
  rw [show -(2 * Real.pi * t * ‖ξ‖) = -(t * (2 * Real.pi * ‖ξ‖)) by ring]
  push_cast
  rfl

private def poissonFrequencyQuotient (t : ℝ) (U : H¹) (ξ : D) : E :=
  (poissonRate t (2 * Real.pi * ‖ξ‖) : ℂ) •
    (𝓕 (isotropicEnergyValue 2 U) : L²) ξ

private theorem poissonFrequencyQuotient_measurable (t : ℝ) (U : H¹) :
    AEStronglyMeasurable (poissonFrequencyQuotient t U) volume := by
  by_cases ht : 0 < t
  · have hc : Continuous (fun ξ : D ↦ (poissonRate t (2 * Real.pi * ‖ξ‖) : ℂ)) := by
      simp only [poissonRate, ite_eq_left ht]
      fun_prop
    exact hc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)
  · change AEStronglyMeasurable
      (fun ξ : D ↦ (poissonRate t (2 * Real.pi * ‖ξ‖) : ℂ) •
        (𝓕 (isotropicEnergyValue 2 U) : L²) ξ) volume
    simp only [poissonRate, ite_eq_right ht, Complex.ofReal_zero, zero_smul]
    exact aestronglyMeasurable_const

private theorem poissonFrequencyQuotient_bound (t : ℝ) (U : H¹) :
    ∀ᵐ ξ, ‖poissonFrequencyQuotient t U ξ - (𝓕 (poissonGenerator U) : L²) ξ‖ ≤
      ‖(𝓕 (poissonGenerator U) : L²) ξ‖ := by
  filter_upwards [fourier_poissonGenerator_ae U] with ξ hg
  have hr : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
  have hb := poissonRate_bounds t hr
  rw [poissonFrequencyQuotient, hg, ← sub_smul, norm_smul, norm_smul]
  rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hb.2), abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right (by linarith [hb.1]) (norm_nonneg _)

private theorem poissonFrequencyQuotient_tendsto (U : H¹) :
    ∀ᵐ ξ, Tendsto (fun t ↦ poissonFrequencyQuotient t U ξ) (𝓝[>] 0)
      (𝓝 ((𝓕 (poissonGenerator U) : L²) ξ)) := by
  filter_upwards [fourier_poissonGenerator_ae U] with ξ hg
  rw [hg]
  change Tendsto (fun t ↦ (poissonRate t (2 * Real.pi * ‖ξ‖) : ℂ) •
    (𝓕 (isotropicEnergyValue 2 U) : L²) ξ) (𝓝[>] 0)
      (𝓝 (((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) • (𝓕 (isotropicEnergyValue 2 U) : L²) ξ))
  simpa only [Function.comp_def] using ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_poissonRate (2 * Real.pi * ‖ξ‖))).smul_const
      ((𝓕 (isotropicEnergyValue 2 U) : L²) ξ)

/-- The actual spatial Poisson operator has its true strong isotropic generator limit. -/
theorem tendsto_poissonDifferenceQuotient (U : H¹) :
    Tendsto (fun t ↦ poissonDifferenceQuotient t U) (𝓝[>] 0) (𝓝 (poissonGenerator U)) := by
  have hF := tendsto_eLpNorm_two_filter_of_dominated
    (fun t ↦ poissonFrequencyQuotient t U) (fun ξ ↦ (𝓕 (poissonGenerator U) : L²) ξ)
    (fun ξ ↦ (𝓕 (poissonGenerator U) : L²) ξ)
    (fun t ↦ poissonFrequencyQuotient_measurable t U)
    (Lp.aestronglyMeasurable _) (Lp.memLp _)
    (Eventually.of_forall fun t ↦ poissonFrequencyQuotient_bound t U)
    (poissonFrequencyQuotient_tendsto U)
  have hclass : Tendsto (fun t ↦ 𝓕 (poissonDifferenceQuotient t U)) (𝓝[>] 0)
      (𝓝 (𝓕 (poissonGenerator U))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    apply hF.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Ioi] at ht
    apply (eLpNorm_congr_ae ?_).symm
    filter_upwards [fourier_poissonDifferenceQuotient_ae ht U] with ξ hξ
    exact congrArg (fun v : E ↦ v - (𝓕 (poissonGenerator U) : L²) ξ) hξ
  simpa only [Function.comp_def, fourierInv_fourier_eq] using continuous_fourierInv.tendsto
    (𝓕 (poissonGenerator U)) |>.comp hclass

/-- Every actual square-integrable norm test has the corresponding genuine generator limit. -/
theorem tendsto_poissonGenerator_inner_test (U : H¹) (W : L²) :
    Tendsto (fun t ↦ (inner ℂ W (poissonDifferenceQuotient t U)).re) (𝓝[>] 0)
      (𝓝 ((inner ℂ W (poissonGenerator U)).re)) := by
  exact Complex.continuous_re.tendsto _ |>.comp
    ((tendsto_const_nhds (x := W)).inner (tendsto_poissonDifferenceQuotient U))

end PartialBalayage.Linear
