/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceComplexBalayage
public import PartialBalayage.Linear.HessianCapEstimate
public import PartialBalayage.Linear.ExtendedLevelSet

/-!
# Unconditional exact Hessian and Beurling weak bounds on genuine L¹ and L² input

Actual whole-space complex balayage constructs the capped density and measurable active set.
Its true weak PDE proves agreement of the full Hessian, traceless Hessian and Beurling
operators outside that set. The exact L² norms and optimized level-set argument give
the article's coefficients for every integrable complex L² input and every level.
No decomposition, regularity, or comparison certificate is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

/-- The actual full Hessian has the article's exact optimized weak coefficient. -/
theorem hessian_levelSet_bound_at_parameter (hn : 2 ≤ n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : Integrable f volume) (α : ℝ≥0∞) :
    α * volume {x | α < ‖hessianL2 f x‖ₑ} ≤
      ENNReal.ofReal (hessianCoefficient n (hessianParameter n)) * ∫⁻ x, ‖f x‖ₑ := by
  apply levelSet_bound_all_of_nnreal
  intro t ht
  let A : ℝ≥0 := ⟨hessianParameter n, (hessianParameter_pos hn).le⟩
  have hA : 0 < A := by exact_mod_cast hessianParameter_pos hn
  let κ : ℝ≥0 := A * t
  have hκ : 0 < κ := mul_pos hA ht
  have hκcoe : (κ : ℝ) = hessianParameter n * (t : ℝ) := rfl
  obtain ⟨ν, s, hs, hcap, _, hmass, hs_mass, _, heq⟩ :=
    exists_complex_hessian_capped_decomposition (by omega) f hf κ hκ
  have hcap' : ∀ᵐ x, ‖ν x‖ ≤ hessianParameter n * (t : ℝ) := by
    simpa only [hκcoe] using hcap
  have hs_mass' : ENNReal.ofReal (hessianParameter n * (t : ℝ)) * volume s ≤
      ∫⁻ x, ‖f x‖ₑ := by
    simpa only [hκcoe] using hs_mass
  exact hessian_levelSet_bound_at_parameter_of_capped_data hn f ν hs ht
    hcap' hmass hs_mass' heq

/-- The full planar Frobenius Hessian has the exact table bound `3 * sqrt 6 / 4`. -/
theorem hessian_levelSet_bound_two
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hf : Integrable f volume) (α : ℝ≥0∞) :
    α * volume {x | α < ‖hessianL2 f x‖ₑ} ≤
      ENNReal.ofReal (3 * Real.sqrt 6 / 4) * ∫⁻ x, ‖f x‖ₑ := by
  simpa only [hessianCoefficient_two] using
    hessian_levelSet_bound_at_parameter (by norm_num : 2 ≤ 2) f hf α

/-- The full complex-input Beurling transform has weak coefficient two at every level. -/
theorem beurling_levelSet_bound
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hf : Integrable f volume) (α : ℝ≥0∞) :
    α * volume {x | α < ‖beurlingL2 f x‖ₑ} ≤ 2 * ∫⁻ x, ‖f x‖ₑ := by
  apply levelSet_bound_all_of_nnreal
  intro t ht
  obtain ⟨ν, s, hs, hcap, hν, hmass, hs_mass, _, hH⟩ :=
    exists_complex_hessian_capped_decomposition (by norm_num) f hf t ht
  have heq := beurling_eq_off_of_hessian_eq f ν hH
  have hT : eLpNorm (beurlingL2 ν) 2 volume ≤ (1 : ℝ≥0∞) * eLpNorm ν 2 volume := by
    exact eLpNorm_le_of_Lp_norm_bound ν (beurlingL2 ν)
      (by simpa only [NNReal.coe_one, one_mul] using norm_beurlingL2_le ν)
  have hcap' : ∀ᵐ x, ‖ν x‖ ≤ (t / 1 : ℝ≥0) := by
    simpa only [div_one] using hcap
  have hs_mass' : ((t / 1 : ℝ≥0) : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ := by
    simpa only [div_one, ENNReal.ofReal_coe_nnreal] using hs_mass
  simpa only [ENNReal.coe_one, mul_one] using
    levelSet_bound_two_mul_of_cap_and_L2_bound hs heq hν ht
      (by norm_num : (0 : ℝ≥0) < 1) hcap' hmass hs_mass' hT

/-- The actual traceless Frobenius Hessian has coefficient `2 * sqrt (1 - 1/n)`. -/
theorem tracelessHessian_levelSet_bound (hn : 2 ≤ n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : Integrable f volume) (α : ℝ≥0∞) :
    α * volume {x | α < ‖tracelessHessianL2CLM n (by omega) f x‖ₑ} ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - 1 / (n : ℝ))) * ∫⁻ x, ‖f x‖ₑ := by
  apply levelSet_bound_all_of_nnreal
  intro t ht
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hq : 0 < 1 - 1 / (n : ℝ) :=
    sub_pos.mpr ((div_lt_one (by positivity : (0 : ℝ) < n)).mpr hnR)
  let M : ℝ≥0 := ⟨Real.sqrt (1 - 1 / (n : ℝ)), Real.sqrt_nonneg _⟩
  have hM : 0 < M := by exact_mod_cast Real.sqrt_pos.mpr hq
  obtain ⟨ν, s, hs, hcap, hν, hmass, hs_mass, hinput, hH⟩ :=
    exists_complex_hessian_capped_decomposition (by omega) f hf (t / M) (div_pos ht hM)
  have heq := tracelessHessian_eq_off_of_hessian_eq (by omega) f ν hinput hH
  have hT : eLpNorm (tracelessHessianL2CLM n (by omega) ν) 2 volume ≤
      (M : ℝ≥0∞) * eLpNorm ν 2 volume :=
    eLpNorm_le_of_Lp_norm_bound ν _ (norm_tracelessHessianL2CLM_apply_le (by omega) ν)
  have hs_mass' : ((t / M : ℝ≥0) : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hs_mass
  have h := levelSet_bound_two_mul_of_cap_and_L2_bound hs heq hν ht hM
    hcap hmass hs_mass' hT
  change _ ≤ ENNReal.ofReal (2 * (M : ℝ)) * ∫⁻ x, ‖f x‖ₑ
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_coe_nnreal]
  exact h

end PartialBalayage.Linear
