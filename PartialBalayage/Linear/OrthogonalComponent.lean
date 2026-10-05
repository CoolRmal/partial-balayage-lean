/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CapEnergy
public import Mathlib.Analysis.Real.Sqrt

/-!
# The level-set estimate from an orthogonal decomposition

The squared-norm estimate off the active set lowers the reduced function's squared threshold by
`κ²/n`. Chebyshev's inequality then gives the coefficient used for the full Hessian in
*Two partial balayage principles*.

The squared-norm and reduced-energy bounds are explicit hypotheses. The Hessian trace identity,
its orthogonal decomposition, and the construction of partial balayage data are separate tasks.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X E F : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {μ : Measure X} {H : X → E} {g : X → F} {s : Set X}

private theorem orthogonal_threshold_lt_aux {n : ℕ} (hn : 0 < n) {t κ : ℝ≥0}
    (hκt : κ < NNReal.sqrt (n : ℝ≥0) * t) : κ ^ (2 : ℕ) / n < t ^ (2 : ℕ) := by
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn
  have hsq := (pow_lt_pow_iff_left₀ zero_le zero_le (by norm_num : (2 : ℕ) ≠ 0)).mpr hκt
  rw [mul_pow, NNReal.sq_sqrt] at hsq
  apply (div_lt_iff₀ hnpos).mpr
  simpa only [mul_comm] using hsq

/-- A squared-norm bound off the active set gives the square-root threshold for the reduced part. -/
theorem measure_norm_gt_le_of_ae_orthogonal_bound (hs : MeasurableSet s) {n : ℕ}
    {t κ : ℝ≥0}
    (horth : ∀ᵐ x ∂μ, x ∉ s →
      ‖H x‖ ^ (2 : ℕ) ≤ ‖g x‖ ^ (2 : ℕ) + (κ : ℝ) ^ (2 : ℕ) / n) :
    μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤ μ s +
      μ {x | (NNReal.sqrt (t ^ (2 : ℕ) - κ ^ (2 : ℕ) / n) : ℝ≥0∞) ≤ ‖g x‖ₑ} := by
  rw [← measure_inter_add_sdiff {x | (t : ℝ≥0∞) < ‖H x‖ₑ} hs]
  refine add_le_add (measure_mono inter_subset_right) (measure_mono_ae ?_)
  filter_upwards [horth] with x hx
  intro hxlevel
  have horth' : ‖H x‖₊ ^ (2 : ℕ) ≤ ‖g x‖₊ ^ (2 : ℕ) + κ ^ (2 : ℕ) / n := by
    exact_mod_cast hx hxlevel.2
  apply ENNReal.coe_le_coe.mpr
  apply (pow_le_pow_iff_left₀ zero_le zero_le (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [NNReal.sq_sqrt]
  apply tsub_le_iff_right.mpr
  have h := (pow_le_pow_left₀ zero_le (ENNReal.coe_lt_coe.mp hxlevel.1).le 2).trans horth'
  simpa only [add_comm] using h

private theorem orthogonal_chebyshev_aux {t D A : ℝ≥0} (hD : 0 < D) {mass : ℝ≥0∞}
    (henergy : eLpNorm g 2 μ ^ (2 : ℕ) ≤ (A : ℝ≥0∞) * mass) :
    (t : ℝ≥0∞) * μ {x | (NNReal.sqrt D : ℝ≥0∞) ≤ ‖g x‖ₑ} ≤
      ((t * A / D : ℝ≥0) : ℝ≥0∞) * mass := by
  have hD0 : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD.ne'
  have hcheb : (D : ℝ≥0∞) * μ {x | (NNReal.sqrt D : ℝ≥0∞) ≤ ‖g x‖ₑ} ≤
      eLpNorm g 2 μ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two, ← ENNReal.coe_pow,
      NNReal.sq_sqrt] using mul_meas_ge_le_pow_eLpNorm' μ (p := 2) (f := g)
        (by norm_num) (by norm_num) (NNReal.sqrt D : ℝ≥0∞)
  calc
    (t : ℝ≥0∞) * μ {x | (NNReal.sqrt D : ℝ≥0∞) ≤ ‖g x‖ₑ} =
        ((t : ℝ≥0∞) / D) * ((D : ℝ≥0∞) *
          μ {x | (NNReal.sqrt D : ℝ≥0∞) ≤ ‖g x‖ₑ}) := by
      simp only [div_eq_mul_inv, mul_assoc,
        ENNReal.inv_mul_cancel_left hD0 ENNReal.coe_ne_top]
    _ ≤ ((t : ℝ≥0∞) / D) * ((A : ℝ≥0∞) * mass) :=
      mul_le_mul_right (hcheb.trans henergy) _
    _ = ((t * A / D : ℝ≥0) : ℝ≥0∞) * mass := by
      rw [ENNReal.coe_div hD.ne', ENNReal.coe_mul]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- The squared-norm and energy hypotheses give the improved Hessian level-set coefficient. -/
theorem levelSet_bound_of_orthogonal_capped_decomposition (hs : MeasurableSet s)
    {n : ℕ} (hn : 2 ≤ n) {t κ : ℝ≥0} (hκ : 0 < κ)
    (hκt : κ < NNReal.sqrt (n : ℝ≥0) * t)
    (horth : ∀ᵐ x ∂μ, x ∉ s →
      ‖H x‖ ^ (2 : ℕ) ≤ ‖g x‖ ^ (2 : ℕ) + (κ : ℝ) ^ (2 : ℕ) / n)
    {mass : ℝ≥0∞} (hs_mass : (κ : ℝ≥0∞) * μ s ≤ mass)
    (henergy : eLpNorm g 2 μ ^ (2 : ℕ) ≤
      ((1 - 1 / (n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * κ * mass) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
      ((t / κ + (1 - 1 / (n : ℝ≥0)) * t * κ /
        (t ^ (2 : ℕ) - κ ^ (2 : ℕ) / n) : ℝ≥0) : ℝ≥0∞) * mass := by
  have hκ0 : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ.ne'
  have hthreshold := orthogonal_threshold_lt_aux (by omega : 0 < n) hκt
  have hset := measure_norm_gt_le_of_ae_orthogonal_bound hs horth (t := t)
  have hactive : (t : ℝ≥0∞) * μ s ≤ (t : ℝ≥0∞) / κ * mass := by
    calc
      (t : ℝ≥0∞) * μ s = (t : ℝ≥0∞) / κ * ((κ : ℝ≥0∞) * μ s) := by
        simp only [div_eq_mul_inv, mul_assoc,
          ENNReal.inv_mul_cancel_left hκ0 ENNReal.coe_ne_top]
      _ ≤ (t : ℝ≥0∞) / κ * mass := mul_le_mul_right hs_mass _
  have henergy' : eLpNorm g 2 μ ^ (2 : ℕ) ≤
      (((1 - 1 / (n : ℝ≥0)) * κ : ℝ≥0) : ℝ≥0∞) * mass := by
    simpa only [ENNReal.coe_mul] using henergy
  have hcheb := orthogonal_chebyshev_aux (t := t) (tsub_pos_iff_lt.mpr hthreshold) henergy'
  calc
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
        (t : ℝ≥0∞) * μ s + (t : ℝ≥0∞) * μ
          {x | (NNReal.sqrt (t ^ (2 : ℕ) - κ ^ (2 : ℕ) / n) : ℝ≥0∞) ≤ ‖g x‖ₑ} := by
      simpa only [mul_add] using mul_le_mul_right hset (t : ℝ≥0∞)
    _ ≤ (t : ℝ≥0∞) / κ * mass +
        ((t * ((1 - 1 / (n : ℝ≥0)) * κ) /
          (t ^ (2 : ℕ) - κ ^ (2 : ℕ) / n) : ℝ≥0) : ℝ≥0∞) * mass :=
      add_le_add hactive hcheb
    _ = ((t / κ + (1 - 1 / (n : ℝ≥0)) * t * κ /
        (t ^ (2 : ℕ) - κ ^ (2 : ℕ) / n) : ℝ≥0) : ℝ≥0∞) * mass := by
      rw [ENNReal.coe_add, ENNReal.coe_div hκ.ne', add_mul]
      congr 2
      ac_rfl

/-- Rescaling the orthogonal coefficient gives the exact scalar objective for the full Hessian. -/
theorem orthogonal_coefficient_rescale {n : ℕ} (hn : 2 ≤ n) {t a : ℝ≥0}
    (ht : 0 < t) (ha : 0 < a) (hna : a < NNReal.sqrt (n : ℝ≥0)) :
    t / (a * t) + (1 - 1 / (n : ℝ≥0)) * t * (a * t) /
        (t ^ (2 : ℕ) - (a * t) ^ (2 : ℕ) / n) =
      1 / a + ((n : ℝ≥0) - 1) * a / ((n : ℝ≥0) - a ^ (2 : ℕ)) := by
  have hnN : 0 < n := by omega
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hnN
  have hn1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hinv : (1 : ℝ≥0) / n ≤ 1 := by
    apply (div_le_iff₀ hnpos).mpr
    simpa only [one_mul] using hn1
  have hna2 := (pow_lt_pow_iff_left₀ zero_le zero_le (by norm_num : (2 : ℕ) ≠ 0)).mpr hna
  rw [NNReal.sq_sqrt] at hna2
  have hthreshold := orthogonal_threshold_lt_aux hnN (mul_lt_mul_of_pos_right hna ht)
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnN.ne'
  have hD0 : (t : ℝ) ^ (2 : ℕ) - (a * t : ℝ≥0) ^ (2 : ℕ) / n ≠ 0 := by
    have h : (a * t : ℝ≥0) ^ (2 : ℕ) / (n : ℝ) < (t : ℝ) ^ (2 : ℕ) := by
      exact_mod_cast hthreshold
    exact (sub_pos.mpr h).ne'
  have hna0 : (n : ℝ) - (a : ℝ) ^ (2 : ℕ) ≠ 0 := by
    have h : (a : ℝ) ^ (2 : ℕ) < n := by exact_mod_cast hna2
    exact (sub_pos.mpr h).ne'
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_sub hinv, NNReal.coe_sub hthreshold.le, NNReal.coe_sub hn1,
    NNReal.coe_sub hna2.le, NNReal.coe_one, NNReal.coe_natCast]
  field_simp

/-- Choosing `κ = a t` gives the article's full-Hessian coefficient from the explicit hypotheses. -/
theorem levelSet_bound_of_orthogonal_parameter (hs : MeasurableSet s)
    {n : ℕ} (hn : 2 ≤ n) {t a : ℝ≥0} (ht : 0 < t) (ha : 0 < a)
    (hna : a < NNReal.sqrt (n : ℝ≥0))
    (horth : ∀ᵐ x ∂μ, x ∉ s →
      ‖H x‖ ^ (2 : ℕ) ≤ ‖g x‖ ^ (2 : ℕ) + (a * t : ℝ≥0) ^ (2 : ℕ) / (n : ℝ))
    {mass : ℝ≥0∞} (hs_mass : ((a * t : ℝ≥0) : ℝ≥0∞) * μ s ≤ mass)
    (henergy : eLpNorm g 2 μ ^ (2 : ℕ) ≤
      ((1 - 1 / (n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * (a * t : ℝ≥0) * mass) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
      ((1 / a + ((n : ℝ≥0) - 1) * a / ((n : ℝ≥0) - a ^ (2 : ℕ)) : ℝ≥0) :
        ℝ≥0∞) * mass := by
  have h := levelSet_bound_of_orthogonal_capped_decomposition hs hn (mul_pos ha ht)
    (mul_lt_mul_of_pos_right hna ht) horth hs_mass henergy
  simpa only [orthogonal_coefficient_rescale hn ht ha hna] using h

/-- On the valid parameter range, the nonnegative coefficient is the ordinary real expression. -/
theorem coe_orthogonal_parameter_coefficient {n : ℕ} (hn : 2 ≤ n) {a : ℝ≥0}
    (hna : a < NNReal.sqrt (n : ℝ≥0)) :
    ((1 / a + ((n : ℝ≥0) - 1) * a / ((n : ℝ≥0) - a ^ (2 : ℕ)) : ℝ≥0) : ℝ) =
      1 / (a : ℝ) + ((n : ℝ) - 1) * a / ((n : ℝ) - (a : ℝ) ^ (2 : ℕ)) := by
  have hn1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hna2 := (pow_lt_pow_iff_left₀ zero_le zero_le (by norm_num : (2 : ℕ) ≠ 0)).mpr hna
  rw [NNReal.sq_sqrt] at hna2
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_sub hn1, NNReal.coe_sub hna2.le, NNReal.coe_one, NNReal.coe_natCast]

end PartialBalayage.Linear
