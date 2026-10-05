/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Complex.Norm

/-!
# Bounded scalar Fourier multipliers on L²

The construction uses Mathlib's unitary L² Fourier transform. It supplies the genuine
complex-input Beurling operator and its L² contraction estimate. Its weak type bound still
requires the capped decomposition and locality proofs and is not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

theorem multiplier_memLp (m : EuclideanSpace ℝ (Fin n) → ℂ)
    (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x ↦ m x * f x) 2 volume := by
  apply (Lp.memLp f).of_le (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards with x
  simpa only [Pi.mul_apply, norm_mul, one_mul] using
    mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))

/-- Pointwise multiplication of an L² function by a measurable scalar symbol of modulus at most 1. -/
def multiplyL2 (m : EuclideanSpace ℝ (Fin n) → ℂ) (hm : Measurable m)
    (hb : ∀ x, ‖m x‖ ≤ 1) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (multiplier_memLp m hm hb f).toLp (fun x ↦ m x * f x)

theorem norm_multiplyL2_le (m : EuclideanSpace ℝ (Fin n) → ℂ) (hm : Measurable m)
    (hb : ∀ x, ‖m x‖ ≤ 1) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖multiplyL2 m hm hb f‖ ≤ ‖f‖ := by
  unfold multiplyL2
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(multiplier_memLp m hm hb f).coeFn_toLp] with x hx
  rw [hx, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))

/-- The L² Fourier multiplier `𝓕⁻¹(m · 𝓕f)` for a measurable symbol of modulus at most 1. -/
def scalarMultiplierL2 (m : EuclideanSpace ℝ (Fin n) → ℂ) (hm : Measurable m)
    (hb : ∀ x, ‖m x‖ ≤ 1) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).symm (multiplyL2 m hm hb (𝓕 f))

theorem norm_scalarMultiplierL2_le (m : EuclideanSpace ℝ (Fin n) → ℂ) (hm : Measurable m)
    (hb : ∀ x, ‖m x‖ ≤ 1) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖scalarMultiplierL2 m hm hb f‖ ≤ ‖f‖ := by
  unfold scalarMultiplierL2
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_multiplyL2_le m hm hb (𝓕 f)).trans (Lp.norm_fourier_eq f).le

/-- The Beurling symbol from the article, with value zero at zero frequency. -/
def beurlingSymbol (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ((ξ 0 : ℂ) - (ξ 1 : ℂ) * Complex.I) ^ 2 / (‖ξ‖ ^ 2 : ℂ)

theorem measurable_beurlingSymbol : Measurable beurlingSymbol := by
  unfold beurlingSymbol
  fun_prop

private theorem norm_beurlingSymbol_aux (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖((ξ 0 : ℂ) - (ξ 1 : ℂ) * Complex.I)‖ ^ 2 = ‖ξ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two, Complex.sub_re, Complex.sub_im, pow_two]

theorem norm_beurlingSymbol_le (ξ : EuclideanSpace ℝ (Fin 2)) : ‖beurlingSymbol ξ‖ ≤ 1 := by
  rw [beurlingSymbol, norm_div, norm_pow, norm_beurlingSymbol_aux, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact div_self_le_one _

/-- The Beurling transform on complex-valued L² functions on the Euclidean plane. -/
def beurlingL2 (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) :=
  scalarMultiplierL2 beurlingSymbol measurable_beurlingSymbol norm_beurlingSymbol_le f

theorem norm_beurlingL2_le (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    ‖beurlingL2 f‖ ≤ ‖f‖ :=
  norm_scalarMultiplierL2_le beurlingSymbol measurable_beurlingSymbol norm_beurlingSymbol_le f

end PartialBalayage.Linear
