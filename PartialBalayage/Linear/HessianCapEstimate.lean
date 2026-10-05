/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.HessianTrace
public import PartialBalayage.Linear.OrthogonalComponent
public import PartialBalayage.Constants.Linear

/-!
# The full Hessian estimate from actual capped data

The energy and Frobenius splitting hypotheses of the abstract orthogonal estimate are discharged
using the actual traceless Hessian and its multiplier norm. Only the concrete capped density,
its mass and active-set bounds, and the off-active equality with the full Hessian remain as
explicit data. Their unconditional construction by partial balayage is a separate requirement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

private theorem sqrt_traceless_coefficient_sq (hn : 2 ≤ n) :
    (⟨Real.sqrt (1 - 1 / (n : ℝ)), Real.sqrt_nonneg _⟩ : ℝ≥0) ^ (2 : ℕ) =
      (1 - 1 / (n : ℝ≥0) : ℝ≥0) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hq : (1 : ℝ) / n ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
    simpa using hnR
  have hqN : (1 : ℝ≥0) / n ≤ 1 := by exact_mod_cast hq
  apply NNReal.coe_injective
  simp only [NNReal.coe_sub hqN,
    NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast]
  exact Real.sq_sqrt (sub_nonneg.mpr hq)

/-- The actual traceless Hessian transports a density's cap and mass to its exact energy bound. -/
theorem tracelessHessian_energy_le_of_cap (hn : 2 ≤ n)
    (ν : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) {κ : ℝ≥0}
    (hcap : ∀ᵐ x ∂volume, ‖ν x‖ ≤ (κ : ℝ)) {mass : ℝ≥0∞}
    (hmass : ∫⁻ x, ‖ν x‖ₑ ≤ mass) :
    eLpNorm (tracelessHessianL2CLM n (by omega) ν) 2 volume ^ (2 : ℕ) ≤
      ((1 - 1 / (n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * κ * mass := by
  let M : ℝ≥0 := ⟨Real.sqrt (1 - 1 / (n : ℝ)), Real.sqrt_nonneg _⟩
  have hnn : ‖tracelessHessianL2CLM n (by omega) ν‖₊ ≤ M * ‖ν‖₊ := by
    exact_mod_cast norm_tracelessHessianL2CLM_apply_le (by omega : 0 < n) ν
  have hT : eLpNorm (tracelessHessianL2CLM n (by omega) ν) 2 volume ≤
      (M : ℝ≥0∞) * eLpNorm ν 2 volume := by
    simpa only [← Lp.enorm_def, enorm, ← ENNReal.coe_mul] using
      ENNReal.coe_le_coe.mpr hnn
  have h := operator_energy_le_of_cap (Lp.aestronglyMeasurable ν) hcap hT hmass
  have hM : M ^ (2 : ℕ) = (1 - 1 / (n : ℝ≥0) : ℝ≥0) :=
    sqrt_traceless_coefficient_sq hn
  simpa only [ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_pow, hM] using h

/-- The actual Hessian has the required reduced squared-norm bound outside the active set. -/
theorem hessian_orthogonal_bound_of_off_active_eq (hn : 2 ≤ n)
    (f ν : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) {κ : ℝ≥0}
    (hcap : ∀ᵐ x ∂volume, ‖ν x‖ ≤ (κ : ℝ)) {s : Set (EuclideanSpace ℝ (Fin n))}
    (heq : ∀ᵐ x ∂volume, x ∉ s → hessianL2 f x = hessianL2 ν x) :
    ∀ᵐ x ∂volume, x ∉ s → ‖hessianL2 f x‖ ^ (2 : ℕ) ≤
      ‖tracelessHessianL2CLM n (by omega) ν x‖ ^ (2 : ℕ) + (κ : ℝ) ^ (2 : ℕ) / n := by
  filter_upwards [heq, hcap, ae_norm_hessianL2_sq (by omega : 0 < n) ν]
    with x hx hκ hsplit
  intro hxs
  rw [hx hxs, hsplit]
  apply add_le_add_right
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hκ 2) (by positivity)

/-- Actual capped density data imply the article's parameterized full-Hessian coefficient. -/
theorem hessian_levelSet_bound_of_capped_data (hn : 2 ≤ n)
    (f ν : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    {t a : ℝ≥0} (ht : 0 < t) (ha : 0 < a) (hna : a < NNReal.sqrt (n : ℝ≥0))
    (hcap : ∀ᵐ x ∂volume, ‖ν x‖ ≤ (a * t : ℝ≥0)) {mass : ℝ≥0∞}
    (hmass : ∫⁻ x, ‖ν x‖ₑ ≤ mass)
    (hs_mass : ((a * t : ℝ≥0) : ℝ≥0∞) * volume s ≤ mass)
    (heq : ∀ᵐ x ∂volume, x ∉ s → hessianL2 f x = hessianL2 ν x) :
    (t : ℝ≥0∞) * volume {x | (t : ℝ≥0∞) < ‖hessianL2 f x‖ₑ} ≤
      ((1 / a + ((n : ℝ≥0) - 1) * a / ((n : ℝ≥0) - a ^ (2 : ℕ)) : ℝ≥0) :
        ℝ≥0∞) * mass := by
  exact levelSet_bound_of_orthogonal_parameter hs hn ht ha hna
    (hessian_orthogonal_bound_of_off_active_eq hn f ν hcap heq) hs_mass
    (tracelessHessian_energy_le_of_cap hn ν hcap hmass)

/-- The article's prescribed minimizer gives its exact Hessian bound from actual capped data. -/
theorem hessian_levelSet_bound_at_parameter_of_capped_data (hn : 2 ≤ n)
    (f ν : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    {t : ℝ≥0} (ht : 0 < t)
    (hcap : ∀ᵐ x ∂volume, ‖ν x‖ ≤ hessianParameter n * (t : ℝ)) {mass : ℝ≥0∞}
    (hmass : ∫⁻ x, ‖ν x‖ₑ ≤ mass)
    (hs_mass : ENNReal.ofReal (hessianParameter n * (t : ℝ)) * volume s ≤ mass)
    (heq : ∀ᵐ x ∂volume, x ∉ s → hessianL2 f x = hessianL2 ν x) :
    (t : ℝ≥0∞) * volume {x | (t : ℝ≥0∞) < ‖hessianL2 f x‖ₑ} ≤
      ENNReal.ofReal (hessianCoefficient n (hessianParameter n)) * mass := by
  let A : ℝ≥0 := ⟨hessianParameter n, (hessianParameter_pos hn).le⟩
  have hA : 0 < A := by exact_mod_cast hessianParameter_pos hn
  have hAn : A < NNReal.sqrt (n : ℝ≥0) := by
    apply NNReal.coe_lt_coe.mp
    rw [Real.coe_sqrt, NNReal.coe_natCast]
    change hessianParameter n < Real.sqrt (n : ℝ)
    exact hessianParameter_lt_sqrt hn
  have hcap' : ∀ᵐ x ∂volume, ‖ν x‖ ≤ (A * t : ℝ≥0) := by
    change ∀ᵐ x ∂volume, ‖ν x‖ ≤ hessianParameter n * (t : ℝ)
    exact hcap
  have hs_mass' : ((A * t : ℝ≥0) : ℝ≥0∞) * volume s ≤ mass := by
    change ENNReal.ofReal ((A * t : ℝ≥0) : ℝ) * volume s ≤ mass at hs_mass
    simpa only [ENNReal.ofReal_coe_nnreal] using hs_mass
  have h := hessian_levelSet_bound_of_capped_data hn f ν hs ht hA hAn
    hcap' hmass hs_mass' heq
  let q : ℝ≥0 := 1 / A + ((n : ℝ≥0) - 1) * A / ((n : ℝ≥0) - A ^ (2 : ℕ))
  have hq : (q : ℝ) = hessianCoefficient n (hessianParameter n) :=
    coe_orthogonal_parameter_coefficient hn hAn
  rw [← hq, ENNReal.ofReal_coe_nnreal]
  exact h

end PartialBalayage.Linear
