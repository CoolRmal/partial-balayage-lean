/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.PowerEnclosure
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Genuine binomial upper bounds for the square generator's beta integral

The rational coefficient recurrence is identified with the actual analytic
binomial series. Its strictly negative tail gives finite polynomial upper
bounds on the half interval without assuming an arithmetic certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- Exact rational coefficients of `(1-t)^(1/5)`. -/
def fifthBinomialCoefficient : ℕ → ℚ
  | 0 => 1
  | n + 1 => ((n : ℚ) - 1 / 5) / (n + 1) * fifthBinomialCoefficient n

/-- The genuine generalized binomial coefficients satisfy their multiplicative recurrence. -/
theorem real_choose_succ (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = (a - n) / (n + 1) * Ring.choose a n := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The rational recurrence is exactly the real analytic binomial coefficient. -/
theorem fifthBinomialCoefficient_eq (n : ℕ) :
    (fifthBinomialCoefficient n : ℝ) = (-1 : ℝ) ^ n * Ring.choose (1 / 5 : ℝ) n := by
  induction n with
  | zero => simp [fifthBinomialCoefficient]
  | succ n ih =>
    simp only [fifthBinomialCoefficient, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, ih,
      real_choose_succ, pow_succ]
    ring

/-- All genuine coefficients after the constant term are nonpositive. -/
theorem fifthBinomialCoefficient_succ_nonpos (n : ℕ) : fifthBinomialCoefficient (n + 1) ≤ 0 := by
  induction n with
  | zero => norm_num [fifthBinomialCoefficient]
  | succ n ih =>
    rw [fifthBinomialCoefficient]
    apply mul_nonpos_of_nonneg_of_nonpos _ ih
    apply div_nonneg
    · have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
    · positivity

/-- The actual fractional power is the sum of the identified rational series. -/
theorem hasSum_fifthBinomial {t : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1) :
    HasSum (fun n ↦ (fifthBinomialCoefficient n : ℝ) * t ^ n) ((1 - t) ^ (1 / 5 : ℝ)) := by
  have hmem : -t ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht] using ht₁
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1 / 5 : ℝ))).hasSum_sub
    hmem
  convert h using 1
  · ext n
    simp only [sub_zero, binomialSeries_apply, List.ofFn_const, List.prod_replicate,
      smul_eq_mul, fifthBinomialCoefficient_eq]
    rw [neg_pow t n]
    ring

/-- Every nonempty finite Taylor truncation bounds the actual power from above. -/
theorem fifth_rpow_le_binomial_sum {t : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    (1 - t) ^ (1 / 5 : ℝ) ≤
      ∑ n ∈ Finset.range N, (fifthBinomialCoefficient n : ℝ) * t ^ n := by
  have hs := (hasSum_fifthBinomial ht ht₁).tendsto_sum_nat
  apply le_of_tendsto hs
  filter_upwards [eventually_ge_atTop N] with m hm
  apply Finset.sum_le_sum_of_subset_of_nonpos (Finset.range_mono hm)
  intro n hn hnN
  have hn' : 1 ≤ n := hN.trans (Nat.le_of_not_gt (by simpa using hnN))
  have hb : fifthBinomialCoefficient n ≤ 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact fifthBinomialCoefficient_succ_nonpos k
  exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hb) (pow_nonneg ht n)

end PartialBalayage.Maximal.Square
