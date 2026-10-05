/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.BetaBinomial

/-!
# Exact finite upper bounds for the actual beta integral

Symmetry halves the interval. Each genuine finite binomial upper bound is
integrated term by term using convergent ordinary real power integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The actual integrand defining `Beta(6/5,6/5)`. -/
def squareBetaIntegrand (t : ℝ) : ℝ := t ^ (1 / 5 : ℝ) * (1 - t) ^ (1 / 5 : ℝ)

/-- The actual convergent real beta integral used by the article's generator constant. -/
def squareBetaIntegral : ℝ := ∫ t in (0 : ℝ)..1, squareBetaIntegrand t

/-- The exact rational sum obtained by integrating the finite binomial series. -/
def betaBinomialSum (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, fifthBinomialCoefficient n / ((2 : ℚ) ^ n * (n + 6 / 5))

theorem continuous_squareBetaIntegrand : Continuous squareBetaIntegrand := by
  unfold squareBetaIntegrand
  exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 5)).mul
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 5)).comp
      (continuous_const.sub continuous_id))

theorem squareBetaIntegrand_sub (t : ℝ) :
    squareBetaIntegrand (1 - t) = squareBetaIntegrand t := by
  simp only [squareBetaIntegrand, sub_sub_cancel, mul_comm]

/-- The actual beta integral is strictly positive. -/
theorem squareBetaIntegral_pos : 0 < squareBetaIntegral := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    continuous_squareBetaIntegrand.continuousOn
  · intro t ht
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by linarith [ht.2]) _)
  · refine ⟨1 / 2, by norm_num, ?_⟩
    unfold squareBetaIntegrand
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by norm_num) _)

/-- Exact symmetry reduces the genuine integral to the half interval. -/
theorem squareBetaIntegral_eq_twice_half :
    squareBetaIntegral = 2 * ∫ t in (0 : ℝ)..(1 / 2), squareBetaIntegrand t := by
  have hs := intervalIntegral.integral_comp_sub_left squareBetaIntegrand 1
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
  simp only [squareBetaIntegrand_sub] at hs
  norm_num only at hs
  have h₀ : IntervalIntegrable squareBetaIntegrand volume (0 : ℝ) (1 / 2) :=
    continuous_squareBetaIntegrand.intervalIntegrable 0 (1 / 2)
  have h₁ : IntervalIntegrable squareBetaIntegrand volume (1 / 2 : ℝ) 1 :=
    continuous_squareBetaIntegrand.intervalIntegrable (1 / 2) 1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h₀ h₁
  unfold squareBetaIntegral
  linarith

/-- Every actual binomial monomial is integrable on the compact half interval. -/
theorem intervalIntegrable_betaMonomial (n : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦
      (fifthBinomialCoefficient n : ℝ) * (t ^ (1 / 5 : ℝ) * t ^ n)) volume 0 (1 / 2) := by
  apply Continuous.intervalIntegrable
  exact continuous_const.mul
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 5)).mul
      (continuous_id.pow n))

/-- The true half-interval monomial integral has its exact rational factor. -/
theorem twice_integral_betaMonomial (n : ℕ) :
    2 * (∫ t in (0 : ℝ)..(1 / 2),
      (fifthBinomialCoefficient n : ℝ) * (t ^ (1 / 5 : ℝ) * t ^ n)) =
      (1 / 2 : ℝ) ^ (1 / 5 : ℝ) *
        ((fifthBinomialCoefficient n / ((2 : ℚ) ^ n * (n + 6 / 5)) : ℚ) : ℝ) := by
  rw [intervalIntegral.integral_const_mul]
  have hi : (∫ t in (0 : ℝ)..(1 / 2), t ^ (1 / 5 : ℝ) * t ^ n) =
      (1 / 2 : ℝ) ^ ((n : ℝ) + 6 / 5) / ((n : ℝ) + 6 / 5) := by
    calc
      _ = ∫ t in (0 : ℝ)..(1 / 2), t ^ ((n : ℝ) + 1 / 5) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        change t ^ (1 / 5 : ℝ) * t ^ n = t ^ ((n : ℝ) + 1 / 5)
        rw [Real.rpow_add ht.1, Real.rpow_natCast]
        exact mul_comm _ _
      _ = _ := by
        rw [integral_rpow (Or.inl (by
          linarith [Nat.cast_nonneg (α := ℝ) n] : -1 < (n : ℝ) + 1 / 5))]
        have hne : (n : ℝ) + 1 / 5 + 1 ≠ 0 := by positivity
        have he : (n : ℝ) + 1 / 5 + 1 = (n : ℝ) + 6 / 5 := by ring
        rw [Real.zero_rpow hne, sub_zero, he]
  rw [hi]
  have hp : (1 / 2 : ℝ) ^ ((n : ℝ) + 6 / 5) =
      (1 / 2 : ℝ) ^ (1 / 5 : ℝ) * (1 / 2 : ℝ) ^ (n + 1 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    congr 1
    push_cast
    ring
  rw [hp]
  push_cast
  rw [div_pow, one_pow, pow_succ]
  have h₂ : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hn : (n : ℝ) + 6 / 5 ≠ 0 := by positivity
  field_simp

/-- Actual finite Taylor upper bounds give exact integrated upper bounds. -/
theorem squareBetaIntegral_le_binomialSum {N : ℕ} (hN : 1 ≤ N) :
    squareBetaIntegral ≤ (1 / 2 : ℝ) ^ (1 / 5 : ℝ) * (betaBinomialSum N : ℝ) := by
  rw [squareBetaIntegral_eq_twice_half]
  have hi : (∫ t in (0 : ℝ)..(1 / 2), squareBetaIntegrand t) ≤
      ∫ t in (0 : ℝ)..(1 / 2),
        ∑ n ∈ Finset.range N,
          (fifthBinomialCoefficient n : ℝ) * (t ^ (1 / 5 : ℝ) * t ^ n) := by
    have hg : IntervalIntegrable (fun t : ℝ ↦ ∑ n ∈ Finset.range N,
        (fifthBinomialCoefficient n : ℝ) * (t ^ (1 / 5 : ℝ) * t ^ n)) volume 0 (1 / 2) := by
      have he : (∑ n ∈ Finset.range N, fun t : ℝ ↦
          (fifthBinomialCoefficient n : ℝ) * (t ^ (1 / 5 : ℝ) * t ^ n)) =
          (fun t : ℝ ↦ ∑ n ∈ Finset.range N,
            (fifthBinomialCoefficient n : ℝ) * (t ^ (1 / 5 : ℝ) * t ^ n)) := by
        ext t
        simp only [Finset.sum_apply]
      rw [← he]
      exact IntervalIntegrable.sum (Finset.range N) (fun n _ ↦ intervalIntegrable_betaMonomial n)
    apply intervalIntegral.integral_mono_on (by norm_num)
      (continuous_squareBetaIntegrand.intervalIntegrable 0 (1 / 2)) hg
    intro t ht
    have h := mul_le_mul_of_nonneg_left (fifth_rpow_le_binomial_sum ht.1
      (by linarith [ht.2]) hN) (Real.rpow_nonneg ht.1 (1 / 5 : ℝ))
    simpa only [squareBetaIntegrand, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    _ ≤ 2 * ∫ t in (0 : ℝ)..(1 / 2),
        ∑ n ∈ Finset.range N,
          (fifthBinomialCoefficient n : ℝ) * (t ^ (1 / 5 : ℝ) * t ^ n) := by linarith
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum
        (fun n _ ↦ intervalIntegrable_betaMonomial n), Finset.mul_sum]
      simp_rw [twice_integral_betaMonomial]
      simp only [betaBinomialSum, Rat.cast_sum, Finset.mul_sum]

end PartialBalayage.Maximal.Square
