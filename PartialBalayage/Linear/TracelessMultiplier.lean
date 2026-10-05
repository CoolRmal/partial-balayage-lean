/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.HessianMultiplier
public import PartialBalayage.Linear.BoundedVectorMultiplier
public import Mathlib.Tactic

/-!
# The traceless second-order Riesz matrix

The Frobenius symbol of the traceless Hessian is the full Hessian symbol plus `I/n` at nonzero
frequency. Its exact norm is `sqrt (1 - 1/n)`. These are supporting `L²` facts; the weak type
estimate still requires the signed balayage and locality arguments.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal ComplexConjugate

namespace PartialBalayage.Linear

variable {n : ℕ}

/-- The identity matrix in complex Frobenius space. -/
def frobeniusIdentity (n : ℕ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij ↦ if ij.1 = ij.2 then 1 else 0)

theorem norm_frobeniusIdentity_sq (n : ℕ) :
    ‖frobeniusIdentity n‖ ^ (2 : ℕ) = (n : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [frobeniusIdentity, Fintype.sum_prod_type]
  simp_rw [apply_ite norm, norm_one, norm_zero]
  simp

theorem inner_frequencyOuterProduct_identity (ξ : EuclideanSpace ℝ (Fin n)) :
    inner ℂ (frequencyOuterProduct ξ) (frobeniusIdentity n) = (‖ξ‖ ^ (2 : ℕ) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [PiLp.inner_apply, frequencyOuterProduct, frobeniusIdentity,
    Fintype.sum_prod_type, RCLike.inner_apply, pow_two]

/-- The traceless Hessian symbol, totalized by zero at zero frequency. -/
def tracelessHessianSymbol (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  if ξ = 0 then 0 else hessianSymbol ξ + ((n : ℂ)⁻¹) • frobeniusIdentity n

theorem measurable_tracelessHessianSymbol :
    Measurable (tracelessHessianSymbol (n := n)) := by
  unfold tracelessHessianSymbol
  exact Measurable.ite (measurableSet_singleton 0)
    measurable_const (measurable_hessianSymbol.add measurable_const)

theorem tracelessHessianSymbol_zero :
    tracelessHessianSymbol (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  simp [tracelessHessianSymbol]

theorem inner_hessianSymbol_identity {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ξ ≠ 0) :
    inner ℂ (hessianSymbol ξ) (frobeniusIdentity n) = -1 := by
  have hnorm : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  rw [hessianSymbol, inner_smul_left, inner_frequencyOuterProduct_identity]
  simp only [map_div₀, map_neg, map_one, map_pow, Complex.conj_ofReal, Complex.ofReal_pow]
  field_simp

theorem norm_tracelessHessianSymbol_sq {ξ : EuclideanSpace ℝ (Fin n)}
    (hn : 0 < n) (hξ : ξ ≠ 0) :
    ‖tracelessHessianSymbol ξ‖ ^ (2 : ℕ) = 1 - 1 / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [tracelessHessianSymbol, ite_eq_right hξ, norm_add_sq (𝕜 := ℂ),
    norm_hessianSymbol_of_ne_zero hξ, inner_smul_right, inner_hessianSymbol_identity hξ,
    norm_smul, mul_pow, norm_frobeniusIdentity_sq]
  change 1 ^ (2 : ℕ) + 2 * (((n : ℂ)⁻¹ * -1).re) +
    ‖(n : ℂ)⁻¹‖ ^ (2 : ℕ) * (n : ℝ) = 1 - 1 / (n : ℝ)
  simp only [one_pow, mul_neg_one, Complex.neg_re, Complex.inv_re,
    Complex.natCast_re, Complex.normSq_natCast, norm_inv, Complex.norm_natCast]
  field_simp
  ring

theorem norm_tracelessHessianSymbol_of_ne_zero {ξ : EuclideanSpace ℝ (Fin n)}
    (hn : 0 < n) (hξ : ξ ≠ 0) :
    ‖tracelessHessianSymbol ξ‖ = Real.sqrt (1 - 1 / (n : ℝ)) := by
  rw [← norm_tracelessHessianSymbol_sq hn hξ, Real.sqrt_sq (norm_nonneg _)]

theorem norm_tracelessHessianSymbol_le (hn : 0 < n) (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖tracelessHessianSymbol ξ‖ ≤ Real.sqrt (1 - 1 / (n : ℝ)) := by
  by_cases hξ : ξ = 0
  · rw [hξ, tracelessHessianSymbol_zero, norm_zero]
    exact Real.sqrt_nonneg _
  · exact (norm_tracelessHessianSymbol_of_ne_zero hn hξ).le

/-- The traceless Hessian as a genuine bounded Fourier operator on `L²`. -/
def tracelessHessianL2CLM (n : ℕ) (hn : 0 < n) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n × Fin n)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  boundedVectorMultiplierL2CLM tracelessHessianSymbol measurable_tracelessHessianSymbol
    ⟨Real.sqrt (1 - 1 / (n : ℝ)), Real.sqrt_nonneg _⟩ (norm_tracelessHessianSymbol_le hn)

theorem norm_tracelessHessianL2CLM_apply_le (hn : 0 < n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖tracelessHessianL2CLM n hn f‖ ≤ Real.sqrt (1 - 1 / (n : ℝ)) * ‖f‖ :=
  norm_boundedVectorMultiplierL2CLM_apply_le tracelessHessianSymbol
    measurable_tracelessHessianSymbol _ (norm_tracelessHessianSymbol_le hn) f

end PartialBalayage.Linear
