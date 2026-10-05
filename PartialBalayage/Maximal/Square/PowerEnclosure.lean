/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Kernel-checked rational enclosures of fifth-root powers

Only exact rational inequalities between fifth powers enter the certificate predicate.
The mathematical soundness theorem connects those decidable checks to the actual real
powers, including the negative integer exponents used in the radial and generator bounds.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Exact rational data bounding the fifth root of an integer power. -/
def IsPowerEnclosure (q : ℚ) (n : ℤ) (lo hi : ℚ) : Prop :=
  0 ≤ lo ∧ lo ^ (5 : ℕ) ≤ q ^ n ∧ q ^ n ≤ hi ^ (5 : ℕ) ∧ 0 ≤ hi

/-- The actual real fractional power has the exact integer fifth-power identity. -/
theorem rpow_div_five_fifth (x : ℝ) (hx : 0 ≤ x) (n : ℤ) :
    (x ^ ((n : ℝ) / 5)) ^ (5 : ℕ) = x ^ n := by
  rw [← Real.rpow_mul_natCast hx ((n : ℝ) / 5) 5]
  norm_num only [Nat.cast_ofNat]
  have hn : (n : ℝ) / 5 * (5 : ℝ) = (n : ℝ) := by ring
  rw [hn, Real.rpow_intCast]

/-- Exact rational fifth-power inequalities enclose the genuine real fractional power. -/
theorem IsPowerEnclosure.rpow_bounds {q lo hi : ℚ} {n : ℤ}
    (h : IsPowerEnclosure q n lo hi) (hq : 0 ≤ q) :
    (lo : ℝ) ≤ (q : ℝ) ^ ((n : ℝ) / 5) ∧
      (q : ℝ) ^ ((n : ℝ) / 5) ≤ (hi : ℝ) := by
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : (0 : ℝ) ≤ lo := by exact_mod_cast h.1
  have hh : (0 : ℝ) ≤ hi := by exact_mod_cast h.2.2.2
  have ht : 0 ≤ (q : ℝ) ^ ((n : ℝ) / 5) := Real.rpow_nonneg hq' _
  constructor
  · apply (pow_le_pow_iff_left₀ hl ht (by decide : (5 : ℕ) ≠ 0)).mp
    rw [rpow_div_five_fifth _ hq' n]
    exact_mod_cast h.2.1
  · apply (pow_le_pow_iff_left₀ ht hh (by decide : (5 : ℕ) ≠ 0)).mp
    rw [rpow_div_five_fifth _ hq' n]
    exact_mod_cast h.2.2.1

end PartialBalayage.Maximal.Square
