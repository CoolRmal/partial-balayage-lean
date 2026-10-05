/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.IsotropicEnergyConstruction
public import PartialBalayage.Linear.PoissonGenerator
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Actual first-order regularization by Poisson averaging

Every positive-height spatial Poisson average of an arbitrary Hilbert L2
input has genuine first-order isotropic energy. Its actual weighted Fourier
coordinate is constructed from the original unitary transform.
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
local notation "H" => PiLp 2 (fun _ : Fin 2 ↦ L²)

/-- The genuine frequency norm times the positive-height multiplier is uniformly bounded. -/
theorem poisson_norm_weight_le {t : ℝ} (ht : 0 < t) (r : ℝ) :
    r * Real.exp (-(2 * Real.pi * t * r)) ≤ (2 * Real.pi * t)⁻¹ := by
  have ha : 0 < 2 * Real.pi * t := by positivity
  have h := (Real.mul_exp_neg_le_exp_neg_one (2 * Real.pi * t * r)).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  rw [inv_eq_one_div]
  apply (le_div_iff₀ ha).mpr
  convert h using 1
  ring

/-- The actual norm-weighted Fourier representative of any positive-height average is in L2. -/
theorem memLp_norm_smul_fourier_poissonConvolutionL2 {t : ℝ} (ht : 0 < t) (f : L²) :
    MemLp (fun ξ : D ↦ ‖ξ‖ • (𝓕 (poissonConvolutionL2 ht f) : L²) ξ) 2 volume := by
  let C : ℝ := (2 * Real.pi * t)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : MemLp (fun ξ : D ↦ C • (𝓕 f : L²) ξ) 2 volume :=
    (Lp.memLp (𝓕 f)).const_smul C
  have hF : ∀ᵐ ξ, (𝓕 (poissonConvolutionL2 ht f) : L²) ξ =
      (poissonOperatorSymbol t ξ) (𝓕 f ξ) := by
    rw [fourier_poissonConvolutionL2 ht]
    exact multiplyOperatorL2_ae (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f)
  apply hm.of_le (continuous_norm.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable (𝓕 (poissonConvolutionL2 ht f))))
  filter_upwards [hF] with ξ hf
  change ‖‖ξ‖ • (𝓕 (poissonConvolutionL2 ht f) : L²) ξ‖ ≤ ‖C • (𝓕 f : L²) ξ‖
  rw [hf]
  simp only [poissonOperatorSymbol, smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg ξ),
    Complex.norm_real, abs_of_pos (Real.exp_pos _), abs_of_nonneg hC]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (poisson_norm_weight_le ht ‖ξ‖) (norm_nonneg _)

/-- The true norm-weighted frequency coordinate of the actual smoothed input. -/
def poissonSmoothedDataTwo {t : ℝ} (ht : 0 < t) (f : L²) : L² :=
  (memLp_norm_smul_fourier_poissonConvolutionL2 ht f).toLp
    (fun ξ : D ↦ ‖ξ‖ • (𝓕 (poissonConvolutionL2 ht f) : L²) ξ)

theorem poissonSmoothedDataTwo_ae {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonSmoothedDataTwo ht f =ᵐ[volume]
      fun ξ : D ↦ ‖ξ‖ • (𝓕 (poissonConvolutionL2 ht f) : L²) ξ :=
  (memLp_norm_smul_fourier_poissonConvolutionL2 ht f).coeFn_toLp

/-- The actual value-data pair of the Poisson smoothed input. -/
def poissonSmoothedPairTwo {t : ℝ} (ht : 0 < t) (f : L²) : H :=
  WithLp.toLp 2 (Fin.cons (poissonConvolutionL2 ht f)
    (fun _ : Fin 1 ↦ poissonSmoothedDataTwo ht f))

theorem poissonSmoothedPairTwo_mem {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonSmoothedPairTwo ht f ∈ isotropicEnergyGraph (X := D) (E := E) 2 := by
  change ∀ᵐ ξ, poissonSmoothedDataTwo ht f ξ =
    ((‖ξ‖ ^ ((2 : ℝ) / 2) : ℝ) : ℂ) • (𝓕 (poissonConvolutionL2 ht f) : L²) ξ
  filter_upwards [poissonSmoothedDataTwo_ae ht f] with ξ hf
  rw [hf]
  norm_num

/-- The genuine first-order energy state of an arbitrary positive-height Poisson average. -/
def poissonSmoothedStateTwo {t : ℝ} (ht : 0 < t) (f : L²) :
    IsotropicEnergySpace (X := D) (E := E) 2 :=
  ⟨poissonSmoothedPairTwo ht f, poissonSmoothedPairTwo_mem ht f⟩

/-- Its physical value is exactly the original normalized spatial Poisson average. -/
theorem isotropicEnergyValue_poissonSmoothedStateTwo {t : ℝ} (ht : 0 < t) (f : L²) :
    isotropicEnergyValue 2 (poissonSmoothedStateTwo ht f) = poissonConvolutionL2 ht f := rfl

end PartialBalayage.Linear
