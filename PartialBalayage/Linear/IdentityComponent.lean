/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CapEnergy

/-!
# The level-set argument with an identity component

This file proves the elementary estimate behind Principle 1.2 of *Two partial balayage principles*.
Outside the active set the original function equals `c • f + g`, where `f` is capped and `g` has a
given `L²` energy bound. The triangle inequality lowers the threshold for `g` by `‖c‖ κ`.

The decomposition and energy estimates are explicit hypotheses. This file does not construct a
signed partial balayage or assert locality of an operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X E 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable [NormedField 𝕜] [NormedSpace 𝕜 E]
variable {μ : Measure X} {H f g : X → E} {s : Set X} {c : 𝕜}

/-- The identity component lowers the reduced function's level threshold by its capped norm. -/
theorem measure_norm_gt_le_of_ae_identity_eq_off (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂μ, x ∉ s → H x = c • f x + g x) {t κ : ℝ≥0}
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ (κ : ℝ)) :
    μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
      μ s + μ {x | ((t - ‖c‖₊ * κ : ℝ≥0) : ℝ≥0∞) ≤ ‖g x‖ₑ} := by
  rw [← measure_inter_add_sdiff {x | (t : ℝ≥0∞) < ‖H x‖ₑ} hs]
  refine add_le_add (measure_mono inter_subset_right) (measure_mono_ae ?_)
  filter_upwards [heq, hcap] with x hx hxcap
  intro hxlevel
  have hf : ‖f x‖₊ ≤ κ := NNReal.coe_le_coe.mp hxcap
  have hnorm : ‖H x‖₊ ≤ ‖c‖₊ * κ + ‖g x‖₊ := by
    rw [hx hxlevel.2]
    calc
      ‖c • f x + g x‖₊ ≤ ‖c • f x‖₊ + ‖g x‖₊ := nnnorm_add_le _ _
      _ ≤ ‖c‖₊ * κ + ‖g x‖₊ := by
        rw [nnnorm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_left hf zero_le) le_rfl
  apply ENNReal.coe_le_coe.mpr
  apply tsub_le_iff_right.mpr
  simpa only [add_comm] using (ENNReal.coe_lt_coe.mp hxlevel.1).le.trans hnorm

private theorem mul_measure_norm_ge_le_of_energy_aux {t δ A : ℝ≥0} (hδ : 0 < δ)
    {mass : ℝ≥0∞} (henergy : eLpNorm g 2 μ ^ (2 : ℕ) ≤ (A : ℝ≥0∞) * mass) :
    (t : ℝ≥0∞) * μ {x | (δ : ℝ≥0∞) ≤ ‖g x‖ₑ} ≤
      ((t * A / δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * mass := by
  have hδ0 : (δ : ℝ≥0∞) ^ (2 : ℕ) ≠ 0 := by simp [hδ.ne']
  have hδtop : (δ : ℝ≥0∞) ^ (2 : ℕ) ≠ ⊤ := by simp
  have hcheb : (δ : ℝ≥0∞) ^ (2 : ℕ) * μ {x | (δ : ℝ≥0∞) ≤ ‖g x‖ₑ} ≤
      eLpNorm g 2 μ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      mul_meas_ge_le_pow_eLpNorm' μ (p := 2) (f := g)
        (by norm_num) (by norm_num) (δ : ℝ≥0∞)
  calc
    (t : ℝ≥0∞) * μ {x | (δ : ℝ≥0∞) ≤ ‖g x‖ₑ} =
        ((t : ℝ≥0∞) * ((δ : ℝ≥0∞) ^ (2 : ℕ))⁻¹) *
          ((δ : ℝ≥0∞) ^ (2 : ℕ) * μ {x | (δ : ℝ≥0∞) ≤ ‖g x‖ₑ}) := by
      simp only [mul_assoc, ENNReal.inv_mul_cancel_left hδ0 hδtop]
    _ ≤ ((t : ℝ≥0∞) * ((δ : ℝ≥0∞) ^ (2 : ℕ))⁻¹) * ((A : ℝ≥0∞) * mass) :=
      mul_le_mul_right (hcheb.trans henergy) _
    _ = ((t * A / δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * mass := by
      rw [ENNReal.coe_div (pow_ne_zero 2 hδ.ne'), ENNReal.coe_mul, ENNReal.coe_pow]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Capped decomposition data with an identity component give the parameterized weak estimate. -/
theorem levelSet_bound_of_identity_capped_decomposition (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂μ, x ∉ s → H x = c • f x + g x)
    {t κ M : ℝ≥0} (hκ : 0 < κ) (hthreshold : ‖c‖₊ * κ < t)
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ (κ : ℝ)) {mass : ℝ≥0∞}
    (hs_mass : (κ : ℝ≥0∞) * μ s ≤ mass)
    (henergy : eLpNorm g 2 μ ^ (2 : ℕ) ≤ (M : ℝ≥0∞) ^ (2 : ℕ) * κ * mass) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
      ((t / κ + t * M ^ (2 : ℕ) * κ / (t - ‖c‖₊ * κ) ^ (2 : ℕ) : ℝ≥0) :
        ℝ≥0∞) * mass := by
  have hκ0 : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ.ne'
  have hset := measure_norm_gt_le_of_ae_identity_eq_off hs heq hcap (t := t)
  have hactive : (t : ℝ≥0∞) * μ s ≤ (t : ℝ≥0∞) / κ * mass := by
    calc
      (t : ℝ≥0∞) * μ s = (t : ℝ≥0∞) / κ * ((κ : ℝ≥0∞) * μ s) := by
        simp only [div_eq_mul_inv, mul_assoc,
          ENNReal.inv_mul_cancel_left hκ0 ENNReal.coe_ne_top]
      _ ≤ (t : ℝ≥0∞) / κ * mass := mul_le_mul_right hs_mass _
  have henergy' : eLpNorm g 2 μ ^ (2 : ℕ) ≤ ((M ^ (2 : ℕ) * κ : ℝ≥0) : ℝ≥0∞) *
      mass := by simpa only [ENNReal.coe_mul, ENNReal.coe_pow] using henergy
  have hcheb := mul_measure_norm_ge_le_of_energy_aux (t := t)
    (tsub_pos_iff_lt.mpr hthreshold) henergy'
  calc
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
        (t : ℝ≥0∞) * μ s + (t : ℝ≥0∞) *
          μ {x | ((t - ‖c‖₊ * κ : ℝ≥0) : ℝ≥0∞) ≤ ‖g x‖ₑ} := by
      simpa only [mul_add] using mul_le_mul_right hset (t : ℝ≥0∞)
    _ ≤ (t : ℝ≥0∞) / κ * mass +
        ((t * (M ^ (2 : ℕ) * κ) / (t - ‖c‖₊ * κ) ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) *
          mass := add_le_add hactive hcheb
    _ = ((t / κ + t * M ^ (2 : ℕ) * κ / (t - ‖c‖₊ * κ) ^ (2 : ℕ) : ℝ≥0) :
        ℝ≥0∞) * mass := by
      rw [ENNReal.coe_add, ENNReal.coe_div hκ.ne', add_mul]
      simp only [mul_assoc]

/-- Setting the cap to `a * t` removes the level from the identity-component coefficient. -/
theorem identity_coefficient_rescale {t a C M : ℝ≥0} (ht : 0 < t) (ha : 0 < a)
    (hCa : C * a < 1) :
    t / (a * t) + t * M ^ (2 : ℕ) * (a * t) / (t - C * (a * t)) ^ (2 : ℕ) =
      1 / a + M ^ (2 : ℕ) * a / (1 - C * a) ^ (2 : ℕ) := by
  have hct : C * (a * t) < t := by
    calc
      C * (a * t) = (C * a) * t := (mul_assoc _ _ _).symm
      _ < 1 * t := mul_lt_mul_of_pos_right hCa ht
      _ = t := one_mul _
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hC0 : (1 : ℝ) - C * a ≠ 0 := by
    have h : (C : ℝ) * a < 1 := by exact_mod_cast hCa
    exact (sub_pos.mpr h).ne'
  have hct0 : (t : ℝ) - C * (a * t) ≠ 0 := by
    have h : (C : ℝ) * (a * t) < t := by exact_mod_cast hct
    exact (sub_pos.mpr h).ne'
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_one, NNReal.coe_sub hct.le, NNReal.coe_sub hCa.le]
  field_simp

/-- The substitution `κ = a t` gives the coefficient in the identity-component principle. -/
theorem levelSet_bound_of_identity_parameter (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂μ, x ∉ s → H x = c • f x + g x)
    {t a M : ℝ≥0} (ht : 0 < t) (ha : 0 < a) (hca : ‖c‖₊ * a < 1)
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ (a * t : ℝ≥0)) {mass : ℝ≥0∞}
    (hs_mass : ((a * t : ℝ≥0) : ℝ≥0∞) * μ s ≤ mass)
    (henergy : eLpNorm g 2 μ ^ (2 : ℕ) ≤
      (M : ℝ≥0∞) ^ (2 : ℕ) * (a * t : ℝ≥0) * mass) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
      ((1 / a + M ^ (2 : ℕ) * a / (1 - ‖c‖₊ * a) ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) *
        mass := by
  have hthreshold : ‖c‖₊ * (a * t) < t := by
    calc
      ‖c‖₊ * (a * t) = (‖c‖₊ * a) * t := (mul_assoc _ _ _).symm
      _ < 1 * t := mul_lt_mul_of_pos_right hca ht
      _ = t := one_mul _
  have h := levelSet_bound_of_identity_capped_decomposition hs heq (mul_pos ha ht)
    hthreshold hcap hs_mass henergy
  simpa only [identity_coefficient_rescale ht ha hca] using h

/-- A genuine `L²` operator bound on the capped density supplies the required reduced energy. -/
theorem levelSet_bound_of_identity_cap_and_L2_bound (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂μ, x ∉ s → H x = c • f x + g x)
    (hf : Integrable f μ) {t κ M : ℝ≥0} (hκ : 0 < κ) (hthreshold : ‖c‖₊ * κ < t)
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ (κ : ℝ)) {mass : ℝ≥0∞}
    (hmass : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ mass) (hs_mass : (κ : ℝ≥0∞) * μ s ≤ mass)
    (hT : eLpNorm g 2 μ ≤ (M : ℝ≥0∞) * eLpNorm f 2 μ) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
      ((t / κ + t * M ^ (2 : ℕ) * κ / (t - ‖c‖₊ * κ) ^ (2 : ℕ) : ℝ≥0) :
        ℝ≥0∞) * mass := by
  apply levelSet_bound_of_identity_capped_decomposition hs heq hκ hthreshold hcap hs_mass
  simpa only [ENNReal.ofReal_coe_nnreal] using
    operator_energy_le_of_cap hf.aestronglyMeasurable hcap hT hmass

end PartialBalayage.Linear
