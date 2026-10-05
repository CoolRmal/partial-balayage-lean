/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonNormEnergy

/-!
# Constructing actual isotropic energy graphs

Finite actual isotropic energy supplies the weighted Fourier `L²` coordinate. The genuine
Poisson norm contraction consequently constructs a norm state in the half-order space.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "H" => PiLp 2 (fun _ : Fin 2 ↦ L²)

/-- The actual isotropic weighted Fourier representative. -/
def isotropicWeightedFourier (α : ℝ) (f : L²) (ξ : D) : E :=
  ((‖ξ‖ ^ (α / 2) : ℝ) : ℂ) • (𝓕 f : L²) ξ

theorem isotropicWeightedFourier_enorm_sq (α : ℝ) (f : L²) (ξ : D) :
    ‖isotropicWeightedFourier α f ξ‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal (‖ξ‖ ^ α) * ‖(𝓕 f : L²) ξ‖ₑ ^ (2 : ℕ) := by
  rw [isotropicWeightedFourier, enorm_smul, mul_pow]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (norm_nonneg ξ) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
  congr 1
  congr 1
  norm_num

/-- Finite actual energy makes the genuine weighted Fourier representative square integrable. -/
theorem memLp_isotropicWeightedFourier (α : ℝ) (f : L²)
    (hE : fourierEnergy α f ≠ ⊤) : MemLp (isotropicWeightedFourier α f) 2 volume := by
  have hw : Measurable (fun ξ : D ↦ ((‖ξ‖ ^ (α / 2) : ℝ) : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable (isotropicWeightedFourier α f) volume :=
    hw.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (𝓕 f))
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hm).mpr
  have hfin : (∫⁻ ξ, ‖isotropicWeightedFourier α f ξ‖ₑ ^ (2 : ℕ)) < ⊤ := by
    simp_rw [isotropicWeightedFourier_enorm_sq]
    exact lt_top_iff_ne_top.mpr hE
  simpa [ENNReal.rpow_two] using hfin

/-- The actual weighted Fourier class constructed from finite energy. -/
def isotropicDataOfFiniteEnergy (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) : L² :=
  (memLp_isotropicWeightedFourier α f hE).toLp (isotropicWeightedFourier α f)

theorem isotropicDataOfFiniteEnergy_ae (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) :
    isotropicDataOfFiniteEnergy α f hE =ᵐ[volume] isotropicWeightedFourier α f :=
  (memLp_isotropicWeightedFourier α f hE).coeFn_toLp

/-- The actual two-coordinate value and weighted Fourier graph. -/
def isotropicPairOfFiniteEnergy (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) : H :=
  WithLp.toLp 2 (Fin.cons f (fun _ : Fin 1 ↦ isotropicDataOfFiniteEnergy α f hE))

theorem isotropicPairOfFiniteEnergy_zero (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) :
    isotropicPairOfFiniteEnergy α f hE 0 = f := rfl

theorem isotropicPairOfFiniteEnergy_one (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) :
    isotropicPairOfFiniteEnergy α f hE 1 = isotropicDataOfFiniteEnergy α f hE := rfl

theorem isotropicPairOfFiniteEnergy_mem (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) :
    isotropicPairOfFiniteEnergy α f hE ∈ isotropicEnergyGraph (X := D) (E := E) α := by
  change ∀ᵐ ξ, isotropicPairOfFiniteEnergy α f hE 1 ξ =
    ((‖ξ‖ ^ (α / 2) : ℝ) : ℂ) • (𝓕 (isotropicPairOfFiniteEnergy α f hE 0) : L²) ξ
  rw [isotropicPairOfFiniteEnergy_one, isotropicPairOfFiniteEnergy_zero]
  exact isotropicDataOfFiniteEnergy_ae α f hE

/-- A genuine energy-space element obtained from finite actual Fourier energy. -/
def isotropicStateOfFiniteEnergy (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) :
    IsotropicEnergySpace (X := D) (E := E) α :=
  ⟨isotropicPairOfFiniteEnergy α f hE, isotropicPairOfFiniteEnergy_mem α f hE⟩

theorem isotropicEnergyValue_isotropicStateOfFiniteEnergy
    (α : ℝ) (f : L²) (hE : fourierEnergy α f ≠ ⊤) :
    isotropicEnergyValue α (isotropicStateOfFiniteEnergy α f hE) = f := rfl

/-- Taking the pointwise norm preserves genuine isotropic half-order energy membership. -/
def isotropicNormStateOne (U : IsotropicEnergySpace (X := D) (E := E) 1) :
    IsotropicEnergySpace (X := D) (E := ℂ) 1 :=
  isotropicStateOfFiniteEnergy 1
    (Complex.ofRealCLM.compLp (poissonNormL2 (isotropicEnergyValue 1 U)))
    (ne_top_of_le_ne_top (fourierEnergy_ne_top 1 U)
      (fourierEnergy_poissonNormL2_le (isotropicEnergyValue 1 U)))

theorem isotropicEnergyValue_isotropicNormStateOne
    (U : IsotropicEnergySpace (X := D) (E := E) 1) :
    isotropicEnergyValue 1 (isotropicNormStateOne U) =
      Complex.ofRealCLM.compLp (poissonNormL2 (isotropicEnergyValue 1 U)) := rfl

/-- The actual norm state's isotropic half-order energy is no larger than the original energy. -/
theorem isotropicEnergyData_normStateOne_le (U : IsotropicEnergySpace (X := D) (E := E) 1) :
    ‖isotropicEnergyData 1 (isotropicNormStateOne U)‖ₑ ^ (2 : ℕ) ≤
      ‖isotropicEnergyData 1 U‖ₑ ^ (2 : ℕ) := by
  rw [isotropicEnergyData_enorm_sq, isotropicEnergyData_enorm_sq,
    isotropicEnergyValue_isotropicNormStateOne]
  exact fourierEnergy_poissonNormL2_le (isotropicEnergyValue 1 U)

end PartialBalayage.Linear
