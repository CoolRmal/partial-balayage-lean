/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonGenerator
public import PartialBalayage.Linear.FourierSobolevGraph

/-!
# Genuine Sobolev regularity of the actual isotropic first-order graph

The actual norm-weighted Fourier coordinate controls the Bessel-weighted transform.
The represented tempered-distribution identity gives genuine order-one Sobolev
membership and therefore an actual physical weak-gradient graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter
open scoped ENNReal SchwartzMap

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := ℂ) 2

/-- The genuine order-one Bessel weight is bounded by one plus the frequency norm. -/
theorem isotropic_bessel_one_weight_le (ξ : D) :
    (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ 1 + ‖ξ‖ := by
  rw [← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [norm_nonneg ξ]⟩

/-- The actual Bessel-weighted Fourier representative of a first-order state lies in L2. -/
theorem memLp_bessel_fourier_isotropicTwo (U : H¹) :
    MemLp (fun ξ : D ↦ (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) •
      (𝓕 (isotropicEnergyValue 2 U) : L²) ξ) 2 volume := by
  have hm := (Lp.memLp (𝓕 (isotropicEnergyValue 2 U))).norm.add
    (Lp.memLp (isotropicEnergyData 2 U)).norm
  have hw : Measurable (fun ξ : D ↦ (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) := by
    fun_prop
  apply hm.of_le (hw.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable (𝓕 (isotropicEnergyValue 2 U))))
  filter_upwards [isotropicEnergyData_two_ae U] with ξ hξ
  change ‖(((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) •
    (𝓕 (isotropicEnergyValue 2 U) : L²) ξ‖ ≤
      ‖‖(𝓕 (isotropicEnergyValue 2 U) : L²) ξ‖ + ‖isotropicEnergyData 2 U ξ‖‖
  rw [hξ]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg ξ), abs_of_nonneg
      (Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg ‖ξ‖)) _),
    abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg ξ)
      (norm_nonneg _)))]
  have h := mul_le_mul_of_nonneg_right (isotropic_bessel_one_weight_le ξ)
    (norm_nonneg ((𝓕 (isotropicEnergyValue 2 U) : L²) ξ))
  nlinarith

/-- The true Bessel Fourier class constructed from the actual isotropic graph. -/
def isotropicBesselDataTwo (U : H¹) : L² :=
  (memLp_bessel_fourier_isotropicTwo U).toLp
    (fun ξ : D ↦ (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) •
      (𝓕 (isotropicEnergyValue 2 U) : L²) ξ)

theorem isotropicBesselDataTwo_ae (U : H¹) :
    isotropicBesselDataTwo U =ᵐ[volume] fun ξ : D ↦
      (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) •
        (𝓕 (isotropicEnergyValue 2 U) : L²) ξ :=
  (memLp_bessel_fourier_isotropicTwo U).coeFn_toLp

/-- Every genuine isotropic first-order state has actual Fourier Sobolev regularity. -/
theorem memSobolev_one_isotropicTwo (U : H¹) :
    TemperedDistribution.MemSobolev 1 2
      (isotropicEnergyValue 2 U : 𝓢'(D, ℂ)) := by
  apply TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mpr
  refine ⟨isotropicBesselDataTwo U, ?_⟩
  rw [Lp.fourier_toTemperedDistribution_eq]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [isotropicBesselDataTwo_ae U] with ξ hξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [smul_eq_mul]
  ring

end PartialBalayage.Linear
