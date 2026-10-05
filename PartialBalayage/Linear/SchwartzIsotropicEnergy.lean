/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonKatoWeak

/-!
# Actual Schwartz tests for the isotropic Poisson generator

Polynomial Schwartz decay constructs the genuine weighted Fourier graph. Real smooth
Schwartz tests therefore belong to the actual generator domain used in weak Kato.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance schwartzIsotropicRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance schwartzIsotropicScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "H" => PiLp 2 (fun _ : Fin 2 ↦ L²)

omit [CompleteSpace E] in
/-- Multiplication of a Schwartz function by the Euclidean norm is square integrable. -/
theorem schwartz_memLp_norm_smul (φ : 𝓢(D, E)) :
    MemLp (fun ξ ↦ ‖ξ‖ • φ ξ) 2 volume := by
  have hweight : (fun ξ : D ↦ (1 + ‖ξ‖ ^ 2 : ℝ)).HasTemperateGrowth := by
    fun_prop
  let ψ := SchwartzMap.smulLeftCLM E (fun ξ : D ↦ (1 + ‖ξ‖ ^ 2 : ℝ)) φ
  apply (ψ.memLp 2 volume).of_le
    (continuous_norm.smul φ.continuous).aestronglyMeasurable
  filter_upwards with ξ
  change ‖‖ξ‖ • φ ξ‖ ≤ ‖ψ ξ‖
  simp only [ψ, SchwartzMap.smulLeftCLM_apply_apply hweight, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg ξ),
    abs_of_nonneg (show (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 by positivity)]
  gcongr
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

/-- The actual norm-weighted Fourier data of a Schwartz function. -/
def schwartzIsotropicDataTwo (φ : 𝓢(D, E)) : L² :=
  (schwartz_memLp_norm_smul (𝓕 φ)).toLp (fun ξ ↦ ‖ξ‖ • (𝓕 φ) ξ)

omit [CompleteSpace E] in
theorem schwartzIsotropicDataTwo_ae (φ : 𝓢(D, E)) :
    schwartzIsotropicDataTwo φ =ᵐ[volume] fun ξ ↦ ‖ξ‖ • (𝓕 φ) ξ :=
  (schwartz_memLp_norm_smul (𝓕 φ)).coeFn_toLp

/-- The actual two-coordinate Schwartz value and weighted Fourier pair. -/
def schwartzIsotropicPairTwo (φ : 𝓢(D, E)) : H :=
  WithLp.toLp 2 (Fin.cons (φ.toLp 2) (fun _ : Fin 1 ↦ schwartzIsotropicDataTwo φ))

omit [CompleteSpace E] in
theorem schwartzIsotropicPairTwo_zero (φ : 𝓢(D, E)) :
    schwartzIsotropicPairTwo φ 0 = φ.toLp 2 := rfl

omit [CompleteSpace E] in
theorem schwartzIsotropicPairTwo_one (φ : 𝓢(D, E)) :
    schwartzIsotropicPairTwo φ 1 = schwartzIsotropicDataTwo φ := rfl

theorem schwartzIsotropicPairTwo_mem (φ : 𝓢(D, E)) :
    schwartzIsotropicPairTwo φ ∈ isotropicEnergyGraph (X := D) (E := E) 2 := by
  change ∀ᵐ ξ, schwartzIsotropicPairTwo φ 1 ξ =
    ((‖ξ‖ ^ ((2 : ℝ) / 2) : ℝ) : ℂ) • (𝓕 (schwartzIsotropicPairTwo φ 0) : L²) ξ
  rw [schwartzIsotropicPairTwo_one, schwartzIsotropicPairTwo_zero]
  rw [SchwartzMap.toLp_fourier_eq]
  filter_upwards [schwartzIsotropicDataTwo_ae φ, (𝓕 φ).coeFn_toLp 2] with ξ hweighted hφ
  rw [hweighted, hφ]
  norm_num

/-- A classical Schwartz function defines an actual isotropic energy state of order two. -/
def schwartzIsotropicStateTwo (φ : 𝓢(D, E)) :
    IsotropicEnergySpace (X := D) (E := E) 2 :=
  ⟨schwartzIsotropicPairTwo φ, schwartzIsotropicPairTwo_mem φ⟩

/-- The actual value of the Schwartz energy graph is the ordinary Schwartz `L²` class. -/
theorem isotropicEnergyValue_schwartzIsotropicStateTwo (φ : 𝓢(D, E)) :
    isotropicEnergyValue 2 (schwartzIsotropicStateTwo φ) = φ.toLp 2 := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- Genuine complexification of a real Schwartz test is compatible with its actual `L²` class. -/
theorem toLp_schwartz_complexify (φ : 𝓢(D, ℝ)) :
    (φ.postcompCLM Complex.ofRealCLM).toLp 2 = Complex.ofRealCLM.compLp (φ.toLp 2) := by
  apply Lp.ext
  filter_upwards [(φ.postcompCLM Complex.ofRealCLM).coeFn_toLp 2,
    Complex.ofRealCLM.coeFn_compLp (φ.toLp 2), φ.coeFn_toLp 2] with x hcomplex hmap hreal
  rw [hcomplex, hmap, hreal]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The genuine scalar test state used in Poisson weak Kato. -/
def realSchwartzIsotropicStateTwo (φ : 𝓢(D, ℝ)) :
    IsotropicEnergySpace (X := D) (E := ℂ) 2 :=
  schwartzIsotropicStateTwo (φ.postcompCLM Complex.ofRealCLM)

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem isotropicEnergyValue_realSchwartzIsotropicStateTwo (φ : 𝓢(D, ℝ)) :
    isotropicEnergyValue 2 (realSchwartzIsotropicStateTwo φ) =
      Complex.ofRealCLM.compLp (φ.toLp 2) :=
  toLp_schwartz_complexify φ

/-- Weak isotropic Kato holds against ordinary real Schwartz tests with the actual norm witness. -/
theorem poisson_generator_weak_kato_schwartz
    (U : IsotropicEnergySpace (X := D) (E := E) 2) (φ : 𝓢(D, ℝ)) (W : L²)
    (hw : ∀ᵐ x, ‖W x‖ ≤ φ x)
    (hs : ∀ᵐ x, (inner ℂ (W x) (isotropicEnergyValue 2 U x)).re =
      φ x * ‖isotropicEnergyValue 2 U x‖) :
    (inner ℂ (Complex.ofRealCLM.compLp (poissonNormL2 (isotropicEnergyValue 2 U)))
      (poissonGenerator (realSchwartzIsotropicStateTwo φ))).re ≤
      (inner ℂ W (poissonGenerator U)).re := by
  apply poisson_generator_weak_kato U (φ.toLp 2) (realSchwartzIsotropicStateTwo φ) W
    (isotropicEnergyValue_realSchwartzIsotropicStateTwo φ)
  · filter_upwards [hw, φ.coeFn_toLp 2] with x hwx hφ
    simpa only [hφ] using hwx
  · filter_upwards [hs, φ.coeFn_toLp 2] with x hsx hφ
    simpa only [hφ] using hsx

end PartialBalayage.Linear
