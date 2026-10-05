/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Exact arithmetic for the proposed square-kernel mass

The supplementary square certificate gives an algebraic mass expression involving `(7 / 4)^(4/5)`.
This file verifies its stated rational bound by enclosing that power between consecutive dyadic
rationals and checking fifth powers exactly. It does not assert that the proposed kernel is
admissible or that its mass bounds a maximal operator.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage

/-- The algebraic mass expression supplied by the supplementary square certificate. -/
def squareCertificateMass : ℝ :=
  (33744736625978973 / 12500000000000000 : ℝ) *
    (7 / 4 : ℝ) ^ (4 / 5 : ℝ) - 3114374068343977777 / 5120000000000000000

private theorem square_radiusPower_fifth :
    ((7 / 4 : ℝ) ^ (4 / 5 : ℝ)) ^ (5 : ℕ) = (7 / 4 : ℝ) ^ (4 : ℕ) := by
  rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (7 / 4 : ℝ)) (4 / 5) 5]
  norm_num [Real.rpow_natCast]

/-- Consecutive dyadic rationals certify the fifth root appearing in the mass expression. -/
theorem square_radiusPower_enclosure :
    (1983489954687375965032826020836 / 1267650600228229401496703205376 : ℝ) ≤
        (7 / 4 : ℝ) ^ (4 / 5 : ℝ) ∧
      (7 / 4 : ℝ) ^ (4 / 5 : ℝ) <
        1983489954687375965032826020837 / 1267650600228229401496703205376 := by
  constructor
  · apply (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [square_radiusPower_fifth]
    norm_num
  · apply (pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [square_radiusPower_fifth]
    norm_num

/-- Exact fifth-root arithmetic gives the rational upper endpoint recorded in the certificate. -/
theorem squareCertificateMass_lt_rational :
    squareCertificateMass <
      (57293825229912685657705034126468225638675935281 : ℝ) /
        15845632502852867518708790067200000000000000000 := by
  have h := mul_lt_mul_of_pos_left square_radiusPower_enclosure.2
    (by norm_num : (0 : ℝ) < 33744736625978973 / 12500000000000000)
  have hs := sub_lt_sub_right h (3114374068343977777 / 5120000000000000000 : ℝ)
  convert hs using 1 <;> norm_num [squareCertificateMass]

/-- The certified algebraic mass is strictly less than the six-decimal rational `3.615749`. -/
theorem squareCertificateMass_lt_3615749 :
    squareCertificateMass < (3615749 / 1000000 : ℝ) := by
  exact lt_trans squareCertificateMass_lt_rational (by norm_num)

/-- In particular, the algebraic mass expression is less than the tabulated `3.616`. -/
theorem squareCertificateMass_lt_3616 : squareCertificateMass < (3616 / 1000 : ℝ) := by
  exact lt_trans squareCertificateMass_lt_3615749 (by norm_num)

end PartialBalayage
