/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonSmoothing

/-!
# Actual first-order states have half-order energy

The genuine first-order graph supplies the square-root frequency coordinate by
an actual L2 domination argument. Its value remains the original physical class.
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
local notation "H¹" => IsotropicEnergySpace (X := D) (E := E) 2

/-- The actual square-root frequency weight is bounded by one plus the norm. -/
theorem isotropic_half_weight_le {r : ℝ} (hr : 0 ≤ r) :
    r ^ ((1 : ℝ) / 2) ≤ 1 + r := by
  by_cases h : r ≤ 1
  · exact (Real.rpow_le_one hr h (by norm_num)).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge h) (by norm_num)).trans
      (by linarith)

/-- The true square-root weighted transform of any first-order state is in L2. -/
theorem memLp_isotropicWeightedFourier_one_of_two (U : H¹) :
    MemLp (isotropicWeightedFourier 1 (isotropicEnergyValue 2 U)) 2 volume := by
  have hm := (Lp.memLp (𝓕 (isotropicEnergyValue 2 U))).norm.add
    (Lp.memLp (isotropicEnergyData 2 U)).norm
  have hw : Measurable (fun ξ : D ↦ ((‖ξ‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) := by
    fun_prop
  apply hm.of_le (hw.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable (𝓕 (isotropicEnergyValue 2 U))))
  filter_upwards [isotropicEnergyData_two_ae U] with ξ hξ
  change ‖((‖ξ‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) •
    (𝓕 (isotropicEnergyValue 2 U) : L²) ξ‖ ≤
      ‖‖(𝓕 (isotropicEnergyValue 2 U) : L²) ξ‖ + ‖isotropicEnergyData 2 U ξ‖‖
  rw [hξ]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg ξ), abs_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _),
    abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg ξ)
      (norm_nonneg _)))]
  have h := mul_le_mul_of_nonneg_right (isotropic_half_weight_le (norm_nonneg ξ))
    (norm_nonneg ((𝓕 (isotropicEnergyValue 2 U) : L²) ξ))
  nlinarith

/-- The actual half-order Fourier data of a first-order state. -/
def isotropicHalfDataOfTwo (U : H¹) : L² :=
  (memLp_isotropicWeightedFourier_one_of_two U).toLp
    (isotropicWeightedFourier 1 (isotropicEnergyValue 2 U))

theorem isotropicHalfDataOfTwo_ae (U : H¹) :
    isotropicHalfDataOfTwo U =ᵐ[volume]
      isotropicWeightedFourier 1 (isotropicEnergyValue 2 U) :=
  (memLp_isotropicWeightedFourier_one_of_two U).coeFn_toLp

/-- The genuine half-order state with the same actual first-order physical value. -/
def isotropicHalfStateOfTwo (U : H¹) : IsotropicEnergySpace (X := D) (E := E) 1 :=
  ⟨WithLp.toLp 2 (Fin.cons (isotropicEnergyValue 2 U)
    (fun _ : Fin 1 ↦ isotropicHalfDataOfTwo U)), isotropicHalfDataOfTwo_ae U⟩

theorem isotropicEnergyValue_isotropicHalfStateOfTwo (U : H¹) :
    isotropicEnergyValue 1 (isotropicHalfStateOfTwo U) = isotropicEnergyValue 2 U := rfl

end PartialBalayage.Linear
