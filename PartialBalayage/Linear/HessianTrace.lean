/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.TracelessMultiplier
public import PartialBalayage.Linear.FourierPostcomposition
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The physical Hessian trace and Frobenius orthogonal splitting

The trace of the full second-order Riesz matrix is minus the input. This identity is proved
for the actual `L²` Fourier operator. The Frobenius identity direction is orthogonal to every
trace-free matrix, giving the squared-norm improvement used in the Hessian level-set bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal NNReal ComplexConjugate

namespace PartialBalayage.Linear

variable {n : ℕ}

/-- Matrix trace as a continuous complex linear functional on Frobenius space. -/
def frobeniusTrace (n : ℕ) : EuclideanSpace ℂ (Fin n × Fin n) →L[ℂ] ℂ :=
  innerSL ℂ (frobeniusIdentity n)

theorem frobeniusTrace_apply (A : EuclideanSpace ℂ (Fin n × Fin n)) :
    frobeniusTrace n A = ∑ i : Fin n, A (i, i) := by
  simp [frobeniusTrace, PiLp.inner_apply, frobeniusIdentity,
    Fintype.sum_prod_type, RCLike.inner_apply]

theorem frobeniusTrace_identity : frobeniusTrace n (frobeniusIdentity n) = (n : ℂ) := by
  simp [frobeniusTrace_apply, frobeniusIdentity]

theorem frobeniusTrace_hessianSymbol {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ξ ≠ 0) :
    frobeniusTrace n (hessianSymbol ξ) = -1 := by
  change inner ℂ (frobeniusIdentity n) (hessianSymbol ξ) = -1
  rw [← inner_conj_symm, inner_hessianSymbol_identity hξ]
  simp

theorem frobeniusTrace_tracelessHessianSymbol (hn : 0 < n)
    (ξ : EuclideanSpace ℝ (Fin n)) : frobeniusTrace n (tracelessHessianSymbol ξ) = 0 := by
  by_cases hξ : ξ = 0
  · simp [hξ, tracelessHessianSymbol_zero]
  · rw [tracelessHessianSymbol, ite_eq_right hξ, map_add, map_smul,
      frobeniusTrace_hessianSymbol hξ, frobeniusTrace_identity]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [hn0]

/-- The trace-free part is orthogonal to the identity component in Frobenius norm. -/
theorem norm_tracefree_add_identity_sq (hn : 0 < n)
    (A : EuclideanSpace ℂ (Fin n × Fin n)) (hA : frobeniusTrace n A = 0) (c : ℂ) :
    ‖A + (c / (n : ℂ)) • frobeniusIdentity n‖ ^ (2 : ℕ) =
      ‖A‖ ^ (2 : ℕ) + ‖c‖ ^ (2 : ℕ) / (n : ℝ) := by
  have hi : inner ℂ A (frobeniusIdentity n) = 0 :=
    inner_eq_zero_symm.mp hA
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, hi, mul_zero]
  simp only [map_zero, mul_zero, add_zero]
  rw [norm_smul, mul_pow, norm_frobeniusIdentity_sq, norm_div, Complex.norm_natCast]
  field_simp

/-- Taking the trace of the complete `L²` Hessian gives minus the input. -/
theorem frobeniusTrace_compLp_hessianL2 (hn : 0 < n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (frobeniusTrace n).compLp (hessianL2 f) = -f := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfreq : (frobeniusTrace n).compLp
      (multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f)) =
        -(𝓕 f) := by
    apply Lp.ext
    have hne : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ξ ≠ 0 := by
      exact volume.ae_ne 0
    filter_upwards [hne, (frobeniusTrace n).coeFn_compLp
      (multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f)),
      (vectorSymbol_memLp hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le
        (𝓕 f)).coeFn_toLp, Lp.coeFn_neg (𝓕 f)] with ξ hξ htrace hm hneg
    rw [htrace, hneg]
    change frobeniusTrace n ((multiplyVectorL2 hessianSymbol measurable_hessianSymbol
      norm_hessianSymbol_le (𝓕 f)) ξ) = -(𝓕 f) ξ
    change frobeniusTrace n (((vectorSymbol_memLp hessianSymbol
      measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f)).toLp _) ξ) = _
    rw [hm, map_smul, frobeniusTrace_hessianSymbol hξ]
    simp
  change (frobeniusTrace n).compLp (𝓕⁻ (multiplyVectorL2 hessianSymbol
    measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f))) = -f
  rw [← fourierInv_compLp, hfreq, fourierInv_neg, fourierInv_fourier_eq]

/-- The scalar identity component `c I/n` as a continuous linear map. -/
def identityTensorCLM (n : ℕ) : ℂ →L[ℂ] EuclideanSpace ℂ (Fin n × Fin n) :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight ((n : ℂ)⁻¹ • frobeniusIdentity n)

theorem identityTensorCLM_apply (c : ℂ) :
    identityTensorCLM n c = (c / (n : ℂ)) • frobeniusIdentity n := by
  simp [identityTensorCLM, smul_smul, div_eq_mul_inv]

/-- The genuine traceless Hessian is the full Hessian plus its scalar identity correction. -/
theorem tracelessHessianL2CLM_eq_hessian_add_identity (hn : 0 < n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    tracelessHessianL2CLM n hn f = hessianL2 f + (identityTensorCLM n).compLp f := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let M : ℝ≥0 := ⟨Real.sqrt (1 - 1 / (n : ℝ)), Real.sqrt_nonneg _⟩
  have hfreq : multiplyBoundedVectorL2 tracelessHessianSymbol
      measurable_tracelessHessianSymbol M (norm_tracelessHessianSymbol_le hn) (𝓕 f) =
        multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f) +
          (identityTensorCLM n).compLp (𝓕 f) := by
    apply Lp.ext
    filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin n)),
      (boundedVectorSymbol_memLp tracelessHessianSymbol measurable_tracelessHessianSymbol M
        (norm_tracelessHessianSymbol_le hn) (𝓕 f)).coeFn_toLp,
      (vectorSymbol_memLp hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le
        (𝓕 f)).coeFn_toLp,
      (identityTensorCLM n).coeFn_compLp (𝓕 f),
      Lp.coeFn_add (multiplyVectorL2 hessianSymbol measurable_hessianSymbol
        norm_hessianSymbol_le (𝓕 f)) ((identityTensorCLM n).compLp (𝓕 f))]
      with ξ hξ hT hH hI hadd
    rw [hadd]
    change ((boundedVectorSymbol_memLp tracelessHessianSymbol measurable_tracelessHessianSymbol M
      (norm_tracelessHessianSymbol_le hn) (𝓕 f)).toLp _) ξ =
        ((vectorSymbol_memLp hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le
          (𝓕 f)).toLp _) ξ + ((identityTensorCLM n).compLp (𝓕 f)) ξ
    rw [hT, hH, hI, identityTensorCLM_apply, tracelessHessianSymbol, ite_eq_right hξ]
    simp only [smul_add, smul_smul, div_eq_mul_inv]
  change 𝓕⁻ (multiplyBoundedVectorL2 tracelessHessianSymbol measurable_tracelessHessianSymbol M
    (norm_tracelessHessianSymbol_le hn) (𝓕 f)) =
      𝓕⁻ (multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f)) +
        (identityTensorCLM n).compLp f
  rw [hfreq, fourierInv_add, fourierInv_compLp, fourierInv_fourier_eq]

/-- The matrix output of the traceless Hessian has zero trace almost everywhere. -/
theorem frobeniusTrace_compLp_tracelessHessianL2CLM (hn : 0 < n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (frobeniusTrace n).compLp (tracelessHessianL2CLM n hn f) = 0 := by
  let M : ℝ≥0 := ⟨Real.sqrt (1 - 1 / (n : ℝ)), Real.sqrt_nonneg _⟩
  have hfreq : (frobeniusTrace n).compLp
      (multiplyBoundedVectorL2 tracelessHessianSymbol measurable_tracelessHessianSymbol M
        (norm_tracelessHessianSymbol_le hn) (𝓕 f)) = 0 := by
    apply Lp.ext
    filter_upwards [(frobeniusTrace n).coeFn_compLp
      (multiplyBoundedVectorL2 tracelessHessianSymbol measurable_tracelessHessianSymbol M
        (norm_tracelessHessianSymbol_le hn) (𝓕 f)),
      (boundedVectorSymbol_memLp tracelessHessianSymbol measurable_tracelessHessianSymbol M
        (norm_tracelessHessianSymbol_le hn) (𝓕 f)).coeFn_toLp,
      Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      with ξ htrace hm hzero
    rw [htrace, hzero]
    change frobeniusTrace n (((boundedVectorSymbol_memLp tracelessHessianSymbol
      measurable_tracelessHessianSymbol M (norm_tracelessHessianSymbol_le hn) (𝓕 f)).toLp _) ξ) = 0
    rw [hm, map_smul, frobeniusTrace_tracelessHessianSymbol hn, smul_zero]
  change (frobeniusTrace n).compLp (𝓕⁻ (multiplyBoundedVectorL2 tracelessHessianSymbol
    measurable_tracelessHessianSymbol M (norm_tracelessHessianSymbol_le hn) (𝓕 f))) = 0
  rw [← fourierInv_compLp, hfreq, fourierInv_zero]

/-- Pointwise trace vanishing for the genuine traceless operator's representatives. -/
theorem ae_frobeniusTrace_tracelessHessianL2CLM_eq_zero (hn : 0 < n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂volume, frobeniusTrace n (tracelessHessianL2CLM n hn f x) = 0 := by
  have h := (frobeniusTrace n).coeFn_compLp (tracelessHessianL2CLM n hn f)
  rw [frobeniusTrace_compLp_tracelessHessianL2CLM hn f] at h
  filter_upwards [h, Lp.coeFn_zero ℂ 2
    (volume : Measure (EuclideanSpace ℝ (Fin n)))] with x hx hzero
  rw [hzero] at hx
  exact hx.symm

/-- The full Hessian's actual pointwise Frobenius norm splits orthogonally almost everywhere. -/
theorem ae_norm_hessianL2_sq (hn : 0 < n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂volume, ‖hessianL2 f x‖ ^ (2 : ℕ) =
      ‖tracelessHessianL2CLM n hn f x‖ ^ (2 : ℕ) + ‖f x‖ ^ (2 : ℕ) / (n : ℝ) := by
  have hsplit := tracelessHessianL2CLM_eq_hessian_add_identity hn f
  filter_upwards [ae_frobeniusTrace_tracelessHessianL2CLM_eq_zero hn f,
    Lp.coeFn_add (hessianL2 f) ((identityTensorCLM n).compLp f),
    (identityTensorCLM n).coeFn_compLp f] with x htrace hadd hI
  have hT : tracelessHessianL2CLM n hn f x =
      hessianL2 f x + (f x / (n : ℂ)) • frobeniusIdentity n := by
    rw [hsplit, hadd, Pi.add_apply, hI, identityTensorCLM_apply]
  have hH : hessianL2 f x = tracelessHessianL2CLM n hn f x +
      (-f x / (n : ℂ)) • frobeniusIdentity n := by
    rw [hT, neg_div, neg_smul]
    module
  rw [hH, norm_tracefree_add_identity_sq hn _ htrace, norm_neg]

end PartialBalayage.Linear
