/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.IsotropicEnergyNesting
public import PartialBalayage.Linear.PoissonSelfAdjoint

/-!
# Genuine half-order form and regularized generator pairings

Actual frequency coordinates identify the half-order form with the spatial generator
against first-order tests. Positive-height regularization gives a symmetric pairing
on every ordinary L2 input.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := E) 2
local notation "Hhalf" => IsotropicEnergySpace (X := D) (E := E) 1

/-- The true half-order data pairing is the actual first-order generator pairing. -/
theorem inner_isotropicHalfDataOfTwo (U : Hhalf) (V : H¹) :
    (2 * Real.pi : ℂ) * inner ℂ (isotropicEnergyData 1 U)
      (isotropicEnergyData 1 (isotropicHalfStateOfTwo V)) =
      inner ℂ (isotropicEnergyValue 1 U) (poissonGenerator V) := by
  rw [← (Lp.fourierTransformₗᵢ D E).inner_map_map
    (isotropicEnergyValue 1 U) (poissonGenerator V)]
  change _ = inner ℂ (𝓕 (isotropicEnergyValue 1 U)) (𝓕 (poissonGenerator V))
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [U.property, isotropicHalfDataOfTwo_ae V,
    fourier_poissonGenerator_ae V] with ξ hU hV hg
  change isotropicEnergyData 1 U ξ =
    ((‖ξ‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • (𝓕 (isotropicEnergyValue 1 U) : L²) ξ at hU
  change isotropicEnergyData 1 (isotropicHalfStateOfTwo V) ξ =
    ((‖ξ‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • (𝓕 (isotropicEnergyValue 2 V) : L²) ξ at hV
  rw [hU, hV, hg, inner_smul_left, inner_smul_right, inner_smul_right,
    Complex.conj_ofReal]
  have hs : (‖ξ‖ ^ ((1 : ℝ) / 2)) * (‖ξ‖ ^ ((1 : ℝ) / 2)) = ‖ξ‖ := by
    rw [← sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
    norm_num
  have hsC : (((‖ξ‖ ^ ((1 : ℝ) / 2)) : ℝ) : ℂ) *
      (((‖ξ‖ ^ ((1 : ℝ) / 2)) : ℝ) : ℂ) = (‖ξ‖ : ℂ) := by
    exact_mod_cast hs
  push_cast
  calc
    _ = (2 * Real.pi : ℂ) *
        ((((‖ξ‖ ^ ((1 : ℝ) / 2)) : ℝ) : ℂ) *
          (((‖ξ‖ ^ ((1 : ℝ) / 2)) : ℝ) : ℂ)) *
          inner ℂ ((𝓕 (isotropicEnergyValue 1 U) : L²) ξ)
            ((𝓕 (isotropicEnergyValue 2 V) : L²) ξ) := by ring
    _ = _ := by rw [hsC]

/-- The true generator of positive-height averaging has its actual scalar Fourier symbol. -/
theorem fourier_poissonSmoothedGenerator_ae {t : ℝ} (ht : 0 < t) (f : L²) :
    ∀ᵐ ξ, (𝓕 (poissonGenerator (poissonSmoothedStateTwo ht f)) : L²) ξ =
      ((2 * Real.pi * ‖ξ‖ * Real.exp (-(2 * Real.pi * t * ‖ξ‖)) : ℝ) : ℂ) •
        (𝓕 f : L²) ξ := by
  have hF : ∀ᵐ ξ, (𝓕 (poissonConvolutionL2 ht f) : L²) ξ =
      (poissonOperatorSymbol t ξ) (𝓕 f ξ) := by
    rw [fourier_poissonConvolutionL2 ht]
    exact multiplyOperatorL2_ae (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f)
  filter_upwards [fourier_poissonGenerator_ae (poissonSmoothedStateTwo ht f), hF]
    with ξ hg hf
  rw [isotropicEnergyValue_poissonSmoothedStateTwo, hf] at hg
  rw [hg]
  simp only [poissonOperatorSymbol, smul_apply, ContinuousLinearMap.id_apply, smul_smul,
    Complex.ofReal_mul]

/-- The actual regularized generator is symmetric on every genuine Hilbert L2 input. -/
theorem inner_poissonSmoothedGenerator {t : ℝ} (ht : 0 < t) (f g : L²) :
    inner ℂ f (poissonGenerator (poissonSmoothedStateTwo ht g)) =
      inner ℂ (poissonGenerator (poissonSmoothedStateTwo ht f)) g := by
  rw [← (Lp.fourierTransformₗᵢ D E).inner_map_map
    f (poissonGenerator (poissonSmoothedStateTwo ht g)),
    ← (Lp.fourierTransformₗᵢ D E).inner_map_map
      (poissonGenerator (poissonSmoothedStateTwo ht f)) g]
  change inner ℂ (𝓕 f) (𝓕 (poissonGenerator (poissonSmoothedStateTwo ht g))) =
    inner ℂ (𝓕 (poissonGenerator (poissonSmoothedStateTwo ht f))) (𝓕 g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourier_poissonSmoothedGenerator_ae ht f,
    fourier_poissonSmoothedGenerator_ae ht g] with ξ hf hg
  rw [hf, hg, inner_smul_right, inner_smul_left, Complex.conj_ofReal]

end PartialBalayage.Linear
