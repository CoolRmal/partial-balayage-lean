/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The vector Riesz transform on L²

A bounded Euclidean-vector symbol acts on scalar complex-valued `L²` functions by scalar
multiplication in Fourier space followed by the vector-valued inverse Fourier transform.
The Riesz symbol is `i ξ / ‖ξ‖`, with value zero at the zero frequency. Its Euclidean norm is one
at every nonzero frequency, which proves the full vector `L²` contraction estimate.

This is a supporting operator construction. The weak type estimate requires the actual capped
decomposition, locality, and extension arguments, which are not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem vectorSymbol_memLp (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι)
    (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x ↦ f x • m x) 2 volume := by
  apply (Lp.memLp f).of_le ((Lp.aestronglyMeasurable f).smul hm.aestronglyMeasurable)
  filter_upwards with x
  change ‖f x • m x‖ ≤ ‖f x‖
  simpa only [norm_smul, mul_one] using
    mul_le_mul_of_nonneg_left (hb x) (norm_nonneg (f x))

/-- Multiplication of a scalar L² function by a measurable Euclidean-vector symbol of norm at most
one. The codomain uses the Euclidean norm. -/
def multiplyVectorL2 (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι)
    (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (vectorSymbol_memLp m hm hb f).toLp (fun x ↦ f x • m x)

theorem norm_multiplyVectorL2_le (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι)
    (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖multiplyVectorL2 m hm hb f‖ ≤ ‖f‖ := by
  unfold multiplyVectorL2
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(vectorSymbol_memLp m hm hb f).coeFn_toLp] with x hx
  rw [hx, norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb x) (norm_nonneg (f x))

/-- The vector-valued Fourier multiplier `𝓕⁻¹((𝓕f) • m)`. -/
def vectorMultiplierL2 (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι)
    (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ ι)).symm
    (multiplyVectorL2 m hm hb (𝓕 f))

theorem norm_vectorMultiplierL2_le (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι)
    (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖vectorMultiplierL2 m hm hb f‖ ≤ ‖f‖ := by
  unfold vectorMultiplierL2
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_multiplyVectorL2_le m hm hb (𝓕 f)).trans (Lp.norm_fourier_eq f).le

/-- The real frequency vector, viewed in the complex Euclidean space. -/
def complexifyEuclidean (ξ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ (ξ i : ℂ))

theorem continuous_complexifyEuclidean :
    Continuous (complexifyEuclidean (n := n)) := by
  unfold complexifyEuclidean
  fun_prop

theorem norm_complexifyEuclidean (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖complexifyEuclidean ξ‖ = ‖ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, complexifyEuclidean,
    Complex.norm_real, Real.norm_eq_abs]

/-- The complete vector Riesz symbol `i ξ / ‖ξ‖`, with totalized value zero at zero frequency. -/
def rieszSymbol (ξ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  (Complex.I / (‖ξ‖ : ℂ)) • complexifyEuclidean ξ

theorem measurable_rieszSymbol : Measurable (rieszSymbol (n := n)) := by
  unfold rieszSymbol
  exact (measurable_const.div (Complex.measurable_ofReal.comp measurable_norm)).smul
    continuous_complexifyEuclidean.measurable

theorem rieszSymbol_zero : rieszSymbol (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  simp [rieszSymbol]

theorem rieszSymbol_apply (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    rieszSymbol ξ i = Complex.I * (ξ i : ℂ) / (‖ξ‖ : ℂ) := by
  simp [rieszSymbol, complexifyEuclidean, div_mul_eq_mul_div]

theorem norm_rieszSymbol_le (ξ : EuclideanSpace ℝ (Fin n)) : ‖rieszSymbol ξ‖ ≤ 1 := by
  rw [rieszSymbol, norm_smul, norm_div, Complex.norm_I, norm_complexifyEuclidean,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using div_self_le_one ‖ξ‖

theorem norm_rieszSymbol_of_ne_zero {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ξ ≠ 0) :
    ‖rieszSymbol ξ‖ = 1 := by
  rw [rieszSymbol, norm_smul, norm_div, Complex.norm_I, norm_complexifyEuclidean,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), one_div]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)

/-- The full vector Riesz transform on complex-valued L² functions on Euclidean space. -/
def rieszL2 (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  vectorMultiplierL2 rieszSymbol measurable_rieszSymbol norm_rieszSymbol_le f

theorem norm_rieszL2_le (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖rieszL2 f‖ ≤ ‖f‖ :=
  norm_vectorMultiplierL2_le rieszSymbol measurable_rieszSymbol norm_rieszSymbol_le f

end PartialBalayage.Linear
