/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.SchwartzIsotropicEnergy

/-!
# Actual measurable norm tests for weak isotropic Kato

The normalized direction, multiplied by a nonnegative scalar test, is an actual `L²` class.
Its norm and inner product satisfy the pointwise hypotheses of weak Poisson Kato.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance poissonNormWitnessRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonNormWitnessScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)

/-- The normalized direction is zero at zero, using total real division. -/
def realNormWitness (a : ℝ) (u : E) : E := (a / ‖u‖) • u

omit [CompleteSpace E] in
theorem norm_realNormWitness_le (a : ℝ) (u : E) : ‖realNormWitness a u‖ ≤ |a| := by
  rw [realNormWitness, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (norm_nonneg u)]
  by_cases hu : ‖u‖ = 0
  · simp only [hu, div_zero, mul_zero]
    exact abs_nonneg a
  · exact (div_mul_cancel₀ |a| hu).le

omit [CompleteSpace E] in
/-- The actual direction is exactly aligned with the vector, including at zero. -/
theorem realNormWitness_inner (a : ℝ) (u : E) :
    (inner ℂ (realNormWitness a u) u).re = a * ‖u‖ := by
  by_cases hu : ‖u‖ = 0
  · have hzero : u = 0 := norm_eq_zero.mp hu
    simp only [hzero, realNormWitness, norm_zero, div_zero, smul_zero, inner_zero_left,
      Complex.zero_re, mul_zero]
  · rw [realNormWitness, inner_smul_left_eq_smul]
    rw [Complex.smul_re, smul_eq_mul]
    have hinner := inner_self_eq_norm_sq (𝕜 := ℂ) u
    rw [RCLike.re_eq_complex_re] at hinner
    rw [hinner]
    field_simp

omit [CompleteSpace E] in
/-- The genuine normalized direction test is square integrable by scalar domination. -/
theorem memLp_realNormWitness (φ : L²ℝ) (f : L²) :
    MemLp (fun x ↦ realNormWitness (φ x) (f x)) 2 volume := by
  apply (Lp.memLp φ).of_le
    (((Lp.aestronglyMeasurable φ).aemeasurable.div
      (Lp.aestronglyMeasurable f).norm.aemeasurable).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable f))
  filter_upwards with x
  change ‖(φ x / ‖f x‖) • f x‖ ≤ ‖φ x‖
  simpa only [realNormWitness, Real.norm_eq_abs] using norm_realNormWitness_le (φ x) (f x)

/-- The actual `L²` norm witness. -/
def poissonNormWitnessL2 (φ : L²ℝ) (f : L²) : L² :=
  (memLp_realNormWitness φ f).toLp (fun x ↦ realNormWitness (φ x) (f x))

omit [CompleteSpace E] in
theorem poissonNormWitnessL2_ae (φ : L²ℝ) (f : L²) :
    poissonNormWitnessL2 φ f =ᵐ[volume] fun x ↦ realNormWitness (φ x) (f x) :=
  (memLp_realNormWitness φ f).coeFn_toLp

omit [CompleteSpace E] in
/-- Nonnegative scalar tests produce an actual norm witness satisfying the Kato cap. -/
theorem norm_poissonNormWitnessL2_le (φ : L²ℝ) (f : L²)
    (hφ : ∀ᵐ x, 0 ≤ φ x) : ∀ᵐ x, ‖poissonNormWitnessL2 φ f x‖ ≤ φ x := by
  filter_upwards [poissonNormWitnessL2_ae φ f, hφ] with x hw hnonneg
  rw [hw]
  simpa only [abs_of_nonneg hnonneg] using norm_realNormWitness_le (φ x) (f x)

omit [CompleteSpace E] in
theorem poissonNormWitnessL2_inner (φ : L²ℝ) (f : L²) :
    ∀ᵐ x, (inner ℂ (poissonNormWitnessL2 φ f x) (f x)).re = φ x * ‖f x‖ := by
  filter_upwards [poissonNormWitnessL2_ae φ f] with x hw
  rw [hw, realNormWitness_inner]

/-- The true generator obeys weak norm Kato for every nonnegative real Schwartz test. -/
theorem poisson_generator_norm_kato_schwartz
    (U : IsotropicEnergySpace (X := D) (E := E) 2) (φ : 𝓢(D, ℝ))
    (hφ : ∀ x, 0 ≤ φ x) :
    (inner ℂ (Complex.ofRealCLM.compLp (poissonNormL2 (isotropicEnergyValue 2 U)))
      (poissonGenerator (realSchwartzIsotropicStateTwo φ))).re ≤
      (inner ℂ (poissonNormWitnessL2 (φ.toLp 2) (isotropicEnergyValue 2 U))
        (poissonGenerator U)).re := by
  apply poisson_generator_weak_kato_schwartz
  · have hnonneg : ∀ᵐ x, 0 ≤ (φ.toLp 2) x := by
      filter_upwards [φ.coeFn_toLp 2] with x hx
      rw [hx]
      exact hφ x
    filter_upwards [norm_poissonNormWitnessL2_le (φ.toLp 2)
      (isotropicEnergyValue 2 U) hnonneg, φ.coeFn_toLp 2] with x hw hx
    simpa only [hx] using hw
  · filter_upwards [poissonNormWitnessL2_inner (φ.toLp 2) (isotropicEnergyValue 2 U),
      φ.coeFn_toLp 2] with x hw hx
    simpa only [hx] using hw

end PartialBalayage.Linear
