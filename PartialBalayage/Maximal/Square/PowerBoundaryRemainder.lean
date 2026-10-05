/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.PowerTaylorRemainder
public import PartialBalayage.Maximal.Square.PowerEnclosure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# The genuine boundary-knot linear remainder bound

Convexity bounds the actual nonnegative remainder by its endpoint values. An ordinary
fifth-power rational check supplies the elementary upper bound for `2^(9/5)`.
-/

@[expose] public section

noncomputable section

open Set

namespace PartialBalayage.Maximal.Square

/-- The actual power's remainder after its linear Taylor polynomial. -/
def powerLinearRemainder (a x : ℝ) : ℝ :=
  x ^ (9 / 5 : ℝ) - (a ^ (9 / 5 : ℝ) + (9 / 5 : ℝ) * a ^ (4 / 5 : ℝ) * (x - a))

theorem rpow_two_nine_fifths_le : (2 : ℝ) ^ (9 / 5 : ℝ) ≤ 18 / 5 := by
  have hc : IsPowerEnclosure 2 9 0 (18 / 5) := by
    unfold IsPowerEnclosure
    decide +kernel
  have hb := hc.rpow_bounds (by norm_num : (0 : ℚ) ≤ 2)
  simpa only [Rat.cast_ofNat, Rat.cast_div, Int.cast_ofNat, Rat.cast_zero] using hb.2

theorem powerLinearRemainder_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ powerLinearRemainder a x := by
  have hconv := convexOn_rpow (by norm_num : (1 : ℝ) ≤ 9 / 5)
  have hd : HasDerivAt (fun t : ℝ ↦ t ^ (9 / 5 : ℝ))
      ((9 / 5 : ℝ) * a ^ (4 / 5 : ℝ)) a := by
    convert Real.hasDerivAt_rpow_const (p := (9 / 5 : ℝ)) (Or.inl ha.ne') using 1
    norm_num
  unfold powerLinearRemainder
  rcases lt_trichotomy x a with h | h | h
  · have hs := hconv.slope_le_of_hasDerivAt hx ha.le h hd
    rw [slope_def_field] at hs
    have hs' := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · rw [h]
    simp
  · have hs := hconv.le_slope_of_hasDerivAt ha.le hx h hd
    rw [slope_def_field] at hs
    have hs' := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

theorem convexOn_powerLinearRemainder (a : ℝ) :
    ConvexOn ℝ (Ici 0) (powerLinearRemainder a) := by
  have hlin : ConcaveOn ℝ (Ici 0) (fun t : ℝ ↦
      a ^ (9 / 5 : ℝ) + (9 / 5 : ℝ) * a ^ (4 / 5 : ℝ) * (t - a)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy u v hu hv huv
    simp only [smul_eq_mul]
    have he := congrArg (fun z : ℝ ↦ z *
      (a ^ (9 / 5 : ℝ) - (9 / 5 : ℝ) * a ^ (4 / 5 : ℝ) * a)) huv
    nlinarith
  exact (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 9 / 5)).sub hlin

private theorem mul_rpow_four_fifths {a : ℝ} (ha : 0 < a) :
    a * a ^ (4 / 5 : ℝ) = a ^ (9 / 5 : ℝ) := by
  calc
    _ = a ^ (1 : ℝ) * a ^ (4 / 5 : ℝ) := by rw [Real.rpow_one]
    _ = a ^ ((1 : ℝ) + 4 / 5) := (Real.rpow_add ha _ _).symm
    _ = _ := by norm_num

/-- The exact boundary error `4/5 * a^(9/5)` on the entire one-sided joining interval. -/
theorem powerLinearRemainder_le {a x : ℝ} (ha : 0 < a) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 2 * a) :
    powerLinearRemainder a x ≤ (4 / 5 : ℝ) * a ^ (9 / 5 : ℝ) := by
  have hp := mul_rpow_four_fifths ha
  have hzero : powerLinearRemainder a 0 = (4 / 5 : ℝ) * a ^ (9 / 5 : ℝ) := by
    unfold powerLinearRemainder
    rw [Real.zero_rpow (by norm_num : (9 / 5 : ℝ) ≠ 0)]
    nlinarith
  have htwo : powerLinearRemainder a (2 * a) ≤ (4 / 5 : ℝ) * a ^ (9 / 5 : ℝ) := by
    have he : powerLinearRemainder a (2 * a) =
        ((2 : ℝ) ^ (9 / 5 : ℝ) - 14 / 5) * a ^ (9 / 5 : ℝ) := by
      unfold powerLinearRemainder
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le]
      nlinarith
    rw [he]
    have hn : 0 ≤ a ^ (9 / 5 : ℝ) := Real.rpow_nonneg ha.le _
    nlinarith [mul_nonneg (sub_nonneg.mpr rpow_two_nine_fifths_le) hn]
  have hs : x ∈ segment ℝ (0 : ℝ) (2 * a) := by
    rw [segment_eq_Icc (by linarith : (0 : ℝ) ≤ 2 * a)]
    exact ⟨hx₀, hx₁⟩
  have hb := (convexOn_powerLinearRemainder a).le_on_segment
    (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show 2 * a ∈ Ici 0 by change 0 ≤ 2 * a; linarith) hs
  rw [hzero] at hb
  exact hb.trans (max_le le_rfl htwo)

theorem abs_powerLinearRemainder_le {a x : ℝ} (ha : 0 < a)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 2 * a) :
    |powerLinearRemainder a x| ≤ (4 / 5 : ℝ) * a ^ (9 / 5 : ℝ) := by
  rw [abs_of_nonneg (powerLinearRemainder_nonneg ha hx₀)]
  exact powerLinearRemainder_le ha hx₀ hx₁

end PartialBalayage.Maximal.Square
