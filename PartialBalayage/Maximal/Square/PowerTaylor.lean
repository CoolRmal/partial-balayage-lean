/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorScaling
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Genuine Taylor coefficients for the certificate's fractional power

The formulas are derivatives of the actual real power function on the positive half-line.
The cubic Taylor polynomial and fourth derivative are identified before any rational
enclosure or rectangle arithmetic is applied.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace PartialBalayage.Maximal.Square

/-- All actual iterated derivatives of a real power at a strictly positive point. -/
theorem iteratedDeriv_real_rpow (p : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun t : ℝ ↦ t ^ p) x =
      (∏ k ∈ Finset.range n, (p - (k : ℝ))) * x ^ (p - (n : ℝ)) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, Finset.range_zero, Finset.prod_empty,
      Nat.cast_zero, sub_zero, one_mul]
  | succ n ih =>
    have heq : iteratedDeriv n (fun t : ℝ ↦ t ^ p) =ᶠ[𝓝 x]
        fun t : ℝ ↦ (∏ k ∈ Finset.range n, (p - (k : ℝ))) * t ^ (p - (n : ℝ)) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd := (Real.hasDerivAt_rpow_const (x := x) (p := p - (n : ℝ))
      (Or.inl hx.ne')).const_mul (∏ k ∈ Finset.range n, (p - (k : ℝ)))
    rw [hd.deriv, Finset.prod_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : p - (n : ℝ) - 1 = p - ((n : ℝ) + 1) := by ring
    rw [hp]
    ring

/-- The actual cubic Taylor polynomial at a positive center. -/
def powerTaylorThree (a x : ℝ) : ℝ :=
  a ^ (9 / 5 : ℝ) + (9 / 5 : ℝ) * a ^ (4 / 5 : ℝ) * (x - a) +
    (18 / 25 : ℝ) * a ^ (-1 / 5 : ℝ) * (x - a) ^ (2 : ℕ) -
      (6 / 125 : ℝ) * a ^ (-6 / 5 : ℝ) * (x - a) ^ (3 : ℕ)

theorem taylorWithinEval_rpow_nine_fifths_three {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) {a : ℝ} (ha : 0 < a) (has : a ∈ s) (x : ℝ) :
    taylorWithinEval (fun t : ℝ ↦ t ^ (9 / 5 : ℝ)) 3 s a x = powerTaylorThree a x := by
  have hcd : ContDiffAt ℝ ω (fun t : ℝ ↦ t ^ (9 / 5 : ℝ)) a :=
    contDiffAt_id.rpow_const_of_ne ha.ne'
  have hi (n : ℕ) : iteratedDerivWithin n (fun t : ℝ ↦ t ^ (9 / 5 : ℝ)) s a =
      (∏ k ∈ Finset.range n, ((9 / 5 : ℝ) - (k : ℝ))) *
        a ^ ((9 / 5 : ℝ) - (n : ℝ)) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hcd.of_le le_top) has,
      iteratedDeriv_real_rpow (9 / 5) n ha]
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [hi]
  norm_num [Finset.prod_range_succ, powerTaylorThree, Nat.factorial, smul_eq_mul]
  ring

theorem iteratedDeriv_four_rpow_nine_fifths {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 4 (fun t : ℝ ↦ t ^ (9 / 5 : ℝ)) x =
      (216 / 625 : ℝ) * x ^ (-11 / 5 : ℝ) := by
  rw [iteratedDeriv_real_rpow (9 / 5) 4 hx]
  norm_num [Finset.prod_range_succ]

end PartialBalayage.Maximal.Square
