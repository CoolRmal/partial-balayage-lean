/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorPrimitive

/-!
# The genuine finite generator integral of a truncated cubic

The actual positive and negative joining points are included by integrability and
ordinary interval additivity. The endpoint correction is the exact power `625/36`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

theorem weighted_truncatedCubicSecondDifference_near {z t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t ≤ z) :
    t ^ (-11 / 5 : ℝ) * truncatedCubicSecondDifference z t =
      6 * z * t ^ (-1 / 5 : ℝ) := by
  rw [truncatedCubicSecondDifference_near_nonneg (ht₀.le.trans ht₁) ht₀.le ht₁]
  have hp : t ^ (-11 / 5 : ℝ) * t ^ (2 : ℕ) = t ^ (-1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht₀]
    congr 1
    norm_num
  calc
    _ = 6 * z * (t ^ (-11 / 5 : ℝ) * t ^ (2 : ℕ)) := by ring
    _ = _ := by rw [hp]

theorem intervalIntegrable_weighted_truncatedCubic_near {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ (-11 / 5 : ℝ) *
      truncatedCubicSecondDifference z t) volume 0 z := by
  apply ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 5)
    (a := 0) (b := z)).const_mul (6 * z)).congr_uIoo
  intro t ht
  rw [uIoo_of_le hz.le] at ht
  exact (weighted_truncatedCubicSecondDifference_near ht.1 ht.2.le).symm

theorem integral_weighted_truncatedCubic_near {z : ℝ} (hz : 0 < z) :
    (∫ t in (0 : ℝ)..z, t ^ (-11 / 5 : ℝ) * truncatedCubicSecondDifference z t) =
      (15 / 2 : ℝ) * z * z ^ (4 / 5 : ℝ) := by
  have heq : (∫ t in (0 : ℝ)..z, t ^ (-11 / 5 : ℝ) *
      truncatedCubicSecondDifference z t) =
      ∫ t in (0 : ℝ)..z, 6 * z * t ^ (-1 / 5 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hz.le] at ht
    by_cases ht₀ : t = 0
    · subst t
      simp only [Real.zero_rpow (by norm_num : (-11 / 5 : ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (-1 / 5 : ℝ) ≠ 0), zero_mul, mul_zero]
    · exact weighted_truncatedCubicSecondDifference_near
        (lt_of_le_of_ne ht.1 (Ne.symm ht₀)) ht.2
  rw [heq, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 5))]
  norm_num only [show (-1 / 5 : ℝ) + 1 = 4 / 5 by norm_num,
    Real.zero_rpow (by norm_num : (4 / 5 : ℝ) ≠ 0), sub_zero]
  ring

theorem intervalIntegrable_weighted_truncatedCubic_near_nonpos {z : ℝ} (hz : z < 0) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ (-11 / 5 : ℝ) *
      truncatedCubicSecondDifference z t) volume 0 (-z) := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ))
    volume 0 (-z)).congr_uIoo
  intro t ht
  rw [uIoo_of_le (neg_nonneg.mpr hz.le)] at ht
  dsimp only
  rw [truncatedCubicSecondDifference_near_nonpos hz.le ht.1.le ht.2.le, mul_zero]

theorem integral_weighted_truncatedCubic_near_nonpos {z : ℝ} (hz : z < 0) :
    (∫ t in (0 : ℝ)..(-z), t ^ (-11 / 5 : ℝ) *
      truncatedCubicSecondDifference z t) = 0 := by
  calc
    _ = ∫ t in (0 : ℝ)..(-z), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (neg_nonneg.mpr hz.le)] at ht
      simp only [truncatedCubicSecondDifference_near_nonpos hz.le ht.1 ht.2, mul_zero]
    _ = 0 := by simp

/-- The actual finite integral, with no generator or arithmetic certificate hypothesis. -/
theorem integral_weighted_truncatedCubic {z T : ℝ} (hT : 0 < T) (hzT : |z| ≤ T) :
    (∫ t in (0 : ℝ)..T, t ^ (-11 / 5 : ℝ) * truncatedCubicSecondDifference z t) =
      truncatedCubicGeneratorPrimitive z T + (625 / 36 : ℝ) * |z| ^ (9 / 5 : ℝ) := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have ha : 0 < |z| := abs_pos.mpr hz.ne
    have hi := intervalIntegrable_weighted_truncatedCubic_far (z := z) ha hzT
    have hn := intervalIntegrable_weighted_truncatedCubic_near_nonpos hz
    rw [← abs_of_neg hz] at hn
    rw [← intervalIntegral.integral_add_adjacent_intervals hn hi,
      abs_of_neg hz, integral_weighted_truncatedCubic_near_nonpos hz,
      integral_weighted_truncatedCubic_far (neg_pos.mpr hz)
        (by simpa only [abs_of_neg hz] using hzT) (by rw [abs_of_neg hz])]
    have hp := truncatedCubicGeneratorPrimitive_at_abs hz.ne
    rw [abs_of_neg hz, max_eq_right hz.le] at hp
    rw [hp]
    ring
  · subst z
    have heq : (∫ t in (0 : ℝ)..T,
        t ^ (-11 / 5 : ℝ) * truncatedCubicSecondDifference 0 t) =
        ∫ t in (0 : ℝ)..T, t ^ (4 / 5 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT.le] at ht
      by_cases ht₀ : t = 0
      · subst t
        simp only [Real.zero_rpow (by norm_num : (-11 / 5 : ℝ) ≠ 0),
          Real.zero_rpow (by norm_num : (4 / 5 : ℝ) ≠ 0), zero_mul]
      · dsimp only
        rw [weighted_truncatedCubicSecondDifference_far (z := 0)
          (lt_of_le_of_ne ht.1 (Ne.symm ht₀)) (by simpa only [abs_zero] using ht.1)]
        simp only [mul_zero, zero_mul, zero_pow (by omega : (2 : ℕ) ≠ 0),
          zero_pow (by omega : (3 : ℕ) ≠ 0), abs_zero, add_zero, sub_zero]
    rw [heq, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 4 / 5))]
    norm_num only [truncatedCubicGeneratorPrimitive, abs_zero, mul_zero, zero_mul,
      zero_pow (by omega : (2 : ℕ) ≠ 0), zero_pow (by omega : (3 : ℕ) ≠ 0),
      show (4 / 5 : ℝ) + 1 = 9 / 5 by norm_num,
      Real.zero_rpow (by norm_num : (9 / 5 : ℝ) ≠ 0), sub_zero, add_zero]
    ring
  · have hi := intervalIntegrable_weighted_truncatedCubic_far (z := z) hz
      (by simpa only [abs_of_pos hz] using hzT)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_weighted_truncatedCubic_near hz) hi,
      integral_weighted_truncatedCubic_near hz,
      integral_weighted_truncatedCubic_far hz
        (by simpa only [abs_of_pos hz] using hzT) (by rw [abs_of_pos hz])]
    have hp := truncatedCubicGeneratorPrimitive_at_abs hz.ne'
    rw [abs_of_pos hz, max_eq_left hz.le] at hp
    rw [hp, abs_of_pos hz]
    ring

theorem intervalIntegrable_weighted_truncatedCubic {z T : ℝ}
    (hT : 0 < T) (hzT : |z| ≤ T) : IntervalIntegrable
      (fun t : ℝ ↦ t ^ (-11 / 5 : ℝ) * truncatedCubicSecondDifference z t) volume 0 T := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · exact (intervalIntegrable_weighted_truncatedCubic_near_nonpos hz).trans
      (intervalIntegrable_weighted_truncatedCubic_far (neg_pos.mpr hz)
        (by simpa only [abs_of_neg hz] using hzT))
  · subst z
    apply (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 4 / 5)
      (a := 0) (b := T)).congr_uIoo
    intro t ht
    rw [uIoo_of_le hT.le] at ht
    have hf := weighted_truncatedCubicSecondDifference_far (z := 0) ht.1
      (by simpa only [abs_zero] using ht.1.le)
    dsimp only
    simpa only [mul_zero, zero_mul, zero_pow (by omega : (2 : ℕ) ≠ 0),
      zero_pow (by omega : (3 : ℕ) ≠ 0), abs_zero, add_zero, sub_zero] using hf.symm
  · exact (intervalIntegrable_weighted_truncatedCubic_near hz).trans
      (intervalIntegrable_weighted_truncatedCubic_far hz
        (by simpa only [abs_of_pos hz] using hzT))

end PartialBalayage.Maximal.Square
