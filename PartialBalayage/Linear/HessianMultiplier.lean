/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.RieszMultiplier

/-!
# The complete second-order Riesz matrix on L²

The matrix Fourier symbol is `-ξᵢ ξⱼ / ‖ξ‖²`. Matrices are represented as the complex Euclidean
space indexed by `Fin n × Fin n`; its norm is the Frobenius norm, rather than the supremum norm
on matrix entries. The symbol has Frobenius norm one away from zero frequency and vanishes at
zero. This yields the full matrix `L²` contraction, a supporting input to the weak type proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

/-- The rank-one frequency matrix `ξ ξᵀ`, viewed in the complex Frobenius space. -/
def frequencyOuterProduct (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij ↦ (ξ ij.1 : ℂ) * (ξ ij.2 : ℂ))

theorem continuous_frequencyOuterProduct :
    Continuous (frequencyOuterProduct (n := n)) := by
  unfold frequencyOuterProduct
  fun_prop

theorem norm_frequencyOuterProduct (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖frequencyOuterProduct ξ‖ = ‖ξ‖ ^ (2 : ℕ) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sq_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, frequencyOuterProduct, EuclideanSpace.real_norm_sq_eq]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, Fintype.sum_prod_type]
  rw [pow_two (∑ i, ξ i ^ (2 : ℕ)), Finset.sum_mul_sum]

/-- The full matrix symbol for `∇²(-Δ)⁻¹`, with zero assigned at zero frequency. -/
def hessianSymbol (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  ((-1 : ℂ) / (‖ξ‖ : ℂ) ^ (2 : ℕ)) • frequencyOuterProduct ξ

theorem measurable_hessianSymbol : Measurable (hessianSymbol (n := n)) := by
  unfold hessianSymbol
  have hm : Measurable (fun ξ : EuclideanSpace ℝ (Fin n) ↦
      (-1 : ℂ) / (‖ξ‖ : ℂ) ^ (2 : ℕ)) := by fun_prop
  exact hm.smul continuous_frequencyOuterProduct.measurable

theorem hessianSymbol_zero : hessianSymbol (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  simp [hessianSymbol]

theorem hessianSymbol_apply (ξ : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    hessianSymbol ξ (i, j) = -(ξ i : ℂ) * (ξ j : ℂ) / (‖ξ‖ : ℂ) ^ (2 : ℕ) := by
  simp [hessianSymbol, frequencyOuterProduct, div_mul_eq_mul_div]

theorem norm_hessianSymbol_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖hessianSymbol ξ‖ ≤ 1 := by
  rw [hessianSymbol, norm_smul, norm_div, norm_neg, norm_one, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    norm_frequencyOuterProduct]
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
    div_self_le_one (‖ξ‖ ^ (2 : ℕ))

theorem norm_hessianSymbol_of_ne_zero {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ξ ≠ 0) :
    ‖hessianSymbol ξ‖ = 1 := by
  rw [hessianSymbol, norm_smul, norm_div, norm_neg, norm_one, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    norm_frequencyOuterProduct, one_div]
  exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))

/-- The full second-order Riesz matrix acting on scalar complex-valued L² functions. -/
def hessianL2 (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  vectorMultiplierL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le f

theorem norm_hessianL2_le (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖hessianL2 f‖ ≤ ‖f‖ :=
  norm_vectorMultiplierL2_le hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le f

end PartialBalayage.Linear
