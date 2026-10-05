/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonQuadraticSpatial
public import PartialBalayage.Linear.IsotropicEnergyConstruction

/-!
# Genuine isotropic Markov contraction

A one-Lipschitz map fixing zero contracts actual spatial increments, hence the genuine
Poisson quadratic defects and their full isotropic half-order energy limit. Its composition
therefore constructs an actual energy graph, with no output membership hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance poissonMarkovRealSpaceE : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonMarkovScalarTowerE : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E
local instance poissonMarkovRealSpaceF : NormedSpace ℝ F :=
  NormedSpace.restrictScalars ℝ ℂ F
local instance poissonMarkovScalarTowerF : IsScalarTower ℝ ℂ F :=
  IsScalarTower.restrictScalars ℝ ℂ F

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²E" => Lp E 2 (volume : Measure D)
local notation "L²F" => Lp F 2 (volume : Measure D)

omit [InnerProductSpace ℂ E] [CompleteSpace E] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- A one-Lipschitz map fixing zero preserves actual square integrability. -/
theorem memLp_poissonMarkov (ψ : E → F) (hψ : LipschitzWith 1 ψ) (h₀ : ψ 0 = 0)
    (f : L²E) : MemLp (fun x ↦ ψ (f x)) 2 volume := by
  apply (Lp.memLp f).of_le (hψ.continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f))
  filter_upwards with x
  simpa only [h₀, sub_zero, NNReal.coe_one, one_mul] using hψ.norm_sub_le (f x) 0

/-- The actual `L²` composition by a one-Lipschitz map fixing zero. -/
def poissonMarkovL2 (ψ : E → F) (hψ : LipschitzWith 1 ψ) (h₀ : ψ 0 = 0) (f : L²E) : L²F :=
  (memLp_poissonMarkov ψ hψ h₀ f).toLp (fun x ↦ ψ (f x))

omit [InnerProductSpace ℂ E] [CompleteSpace E] [InnerProductSpace ℂ F] [CompleteSpace F] in
theorem poissonMarkovL2_ae (ψ : E → F) (hψ : LipschitzWith 1 ψ) (h₀ : ψ 0 = 0)
    (f : L²E) : poissonMarkovL2 ψ hψ h₀ f =ᵐ[volume] fun x ↦ ψ (f x) :=
  (memLp_poissonMarkov ψ hψ h₀ f).coeFn_toLp

omit [InnerProductSpace ℂ E] [CompleteSpace E] [InnerProductSpace ℂ F] [CompleteSpace F] in
theorem poissonMarkovL2_pair_ae (ψ : E → F) (hψ : LipschitzWith 1 ψ) (h₀ : ψ 0 = 0)
    (f : L²E) {t : ℝ} (ht : 0 < t) : ∀ᵐ p ∂poissonPairMeasure t,
      poissonMarkovL2 ψ hψ h₀ f p.1 = ψ (f p.1) ∧
      poissonMarkovL2 ψ hψ h₀ f (p.1 - p.2) = ψ (f (p.1 - p.2)) := by
  let := PartialBalayage.isProbabilityMeasure_poissonKernelMeasure n ht
  let g := poissonMarkovL2 ψ hψ h₀ f
  have he := poissonMarkovL2_ae ψ hψ h₀ f
  have hf : StronglyMeasurable (fun p : D × D ↦ ψ (f (p.1 - p.2))) :=
    hψ.continuous.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop))
  have hg : StronglyMeasurable (fun p : D × D ↦ g (p.1 - p.2)) :=
    (Lp.stronglyMeasurable g).comp_measurable (by fun_prop)
  have hset : MeasurableSet {p : D × D | g (p.1 - p.2) = ψ (f (p.1 - p.2))} := by
    simpa only [Pi.sub_apply, norm_eq_zero, sub_eq_zero] using
      measurableSet_eq_fun (hg.sub hf).norm.measurable
        (measurable_const (a := (0 : ℝ)))
  have hfirst : ∀ᵐ p ∂poissonPairMeasure t, g p.1 = ψ (f p.1) :=
    he.comp_tendsto (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure D))
      (ν := PartialBalayage.poissonKernelMeasure n t)).tendsto_ae
  have hsecond : ∀ᵐ p ∂poissonPairMeasure t, g (p.1 - p.2) = ψ (f (p.1 - p.2)) := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    filter_upwards with x
    exact (withDensity_absolutelyContinuous volume
      (fun y ↦ ENNReal.ofReal (PartialBalayage.poissonKernel n t y))).ae_le
        (he.comp_tendsto (volume.measurePreserving_sub_left x).quasiMeasurePreserving.tendsto_ae)
  filter_upwards [hfirst, hsecond] with p hfirst hsecond
  exact ⟨hfirst, hsecond⟩

/-- Actual Poisson quadratic defects contract under every one-Lipschitz map fixing zero. -/
theorem poissonQuadraticDefect_markov_le (ψ : E → F) (hψ : LipschitzWith 1 ψ)
    (h₀ : ψ 0 = 0) {t : ℝ} (ht : 0 < t) (f : L²E) :
    poissonQuadraticDefect ht (poissonMarkovL2 ψ hψ h₀ f) ≤ poissonQuadraticDefect ht f := by
  rw [poissonQuadraticDefect_eq_increment_integral,
    poissonQuadraticDefect_eq_increment_integral]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (integrable_poisson_increment_sq ht _)
    (integrable_poisson_increment_sq ht f)
  filter_upwards [poissonMarkovL2_pair_ae ψ hψ h₀ f ht] with p hp
  rw [hp.1, hp.2]
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa only [NNReal.coe_one, one_mul] using hψ.norm_sub_le (f p.1) (f (p.1 - p.2))

/-- The full genuine isotropic half-order energy has the Markov contraction property. -/
theorem fourierEnergy_poissonMarkovL2_le (ψ : E → F) (hψ : LipschitzWith 1 ψ)
    (h₀ : ψ 0 = 0) (f : L²E) :
    fourierEnergy 1 (poissonMarkovL2 ψ hψ h₀ f) ≤ fourierEnergy 1 f := by
  have h : ENNReal.ofReal (2 * Real.pi) * fourierEnergy 1 (poissonMarkovL2 ψ hψ h₀ f) ≤
      ENNReal.ofReal (2 * Real.pi) * fourierEnergy 1 f := by
    apply le_of_tendsto_of_tendsto (tendsto_poissonQuadraticSpectral _)
      (tendsto_poissonQuadraticSpectral f)
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [poissonQuadraticSpectral_eq_ofReal ht, poissonQuadraticSpectral_eq_ofReal ht]
    exact ENNReal.ofReal_le_ofReal (poissonQuadraticDefect_markov_le ψ hψ h₀ ht f)
  have hc : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by positivity
  have hcancel := mul_le_mul' (le_refl (ENNReal.ofReal (2 * Real.pi))⁻¹) h
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_mul]
    using hcancel

/-- A one-Lipschitz composition fixing zero defines a genuine half-order energy state. -/
def isotropicMarkovStateOne (ψ : E → F) (hψ : LipschitzWith 1 ψ) (h₀ : ψ 0 = 0)
    (U : IsotropicEnergySpace (X := D) (E := E) 1) :
    IsotropicEnergySpace (X := D) (E := F) 1 :=
  isotropicStateOfFiniteEnergy 1 (poissonMarkovL2 ψ hψ h₀ (isotropicEnergyValue 1 U))
    (ne_top_of_le_ne_top (fourierEnergy_ne_top 1 U)
      (fourierEnergy_poissonMarkovL2_le ψ hψ h₀ (isotropicEnergyValue 1 U)))

theorem isotropicEnergyValue_isotropicMarkovStateOne
    (ψ : E → F) (hψ : LipschitzWith 1 ψ) (h₀ : ψ 0 = 0)
    (U : IsotropicEnergySpace (X := D) (E := E) 1) :
    isotropicEnergyValue 1 (isotropicMarkovStateOne ψ hψ h₀ U) =
      poissonMarkovL2 ψ hψ h₀ (isotropicEnergyValue 1 U) := rfl

theorem isotropicEnergyData_markovStateOne_le (ψ : E → F) (hψ : LipschitzWith 1 ψ)
    (h₀ : ψ 0 = 0) (U : IsotropicEnergySpace (X := D) (E := E) 1) :
    ‖isotropicEnergyData 1 (isotropicMarkovStateOne ψ hψ h₀ U)‖ₑ ^ (2 : ℕ) ≤
      ‖isotropicEnergyData 1 U‖ₑ ^ (2 : ℕ) := by
  rw [isotropicEnergyData_enorm_sq, isotropicEnergyData_enorm_sq,
    isotropicEnergyValue_isotropicMarkovStateOne]
  exact fourierEnergy_poissonMarkovL2_le ψ hψ h₀ (isotropicEnergyValue 1 U)

end PartialBalayage.Linear
