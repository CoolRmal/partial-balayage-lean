/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.RieszMultiplier
public import Mathlib.Tactic

/-!
# Bounded vector Fourier multipliers as continuous linear maps

The multiplier is scalar in its input and Euclidean-vector valued in its output. Its norm is
bounded by the pointwise symbol bound, with any nonnegative coefficient, including zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- A bounded measurable vector symbol preserves square integrability. -/
theorem boundedVectorSymbol_memLp
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ))
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x ↦ f x • m x) 2 volume := by
  apply ((Lp.memLp f).const_smul (M : ℂ)).of_le
    ((Lp.aestronglyMeasurable f).smul hm.aestronglyMeasurable)
  filter_upwards with x
  change ‖f x • m x‖ ≤ ‖(M : ℂ) • f x‖
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg M.coe_nonneg]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb x) (norm_nonneg (f x))

/-- Pointwise multiplication by a bounded vector symbol on the actual `L²` spaces. -/
def multiplyBoundedVectorL2
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ))
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (boundedVectorSymbol_memLp m hm M hb f).toLp (fun x ↦ f x • m x)

theorem norm_multiplyBoundedVectorL2_le
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ))
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖multiplyBoundedVectorL2 m hm M hb f‖ ≤ (M : ℝ) * ‖f‖ := by
  have hbound : ‖multiplyBoundedVectorL2 m hm M hb f‖ ≤ ‖(M : ℂ) • f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(boundedVectorSymbol_memLp m hm M hb f).coeFn_toLp,
      Lp.coeFn_smul (M : ℂ) f] with x hx hs
    change ‖((boundedVectorSymbol_memLp m hm M hb f).toLp _) x‖ ≤ ‖((M : ℂ) • f) x‖
    rw [hs, hx]
    change ‖f x • m x‖ ≤ ‖(M : ℂ) • f x‖
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg M.coe_nonneg]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb x) (norm_nonneg (f x))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg M.coe_nonneg] using hbound

/-- Multiplication by the symbol is complex linear. -/
def multiplyBoundedVectorL2Linear
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ[ℂ]
      Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun := multiplyBoundedVectorL2 m hm M hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(boundedVectorSymbol_memLp m hm M hb (f + g)).coeFn_toLp,
      (boundedVectorSymbol_memLp m hm M hb f).coeFn_toLp,
      (boundedVectorSymbol_memLp m hm M hb g).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add (multiplyBoundedVectorL2 m hm M hb f)
        (multiplyBoundedVectorL2 m hm M hb g)] with x hfg hf hg hsum hsum'
    rw [hsum']
    change ((boundedVectorSymbol_memLp m hm M hb (f + g)).toLp _) x =
      ((boundedVectorSymbol_memLp m hm M hb f).toLp _) x +
        ((boundedVectorSymbol_memLp m hm M hb g).toLp _) x
    rw [hfg, hf, hg, hsum]
    exact add_smul (f x) (g x) (m x)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(boundedVectorSymbol_memLp m hm M hb (c • f)).coeFn_toLp,
      (boundedVectorSymbol_memLp m hm M hb f).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (multiplyBoundedVectorL2 m hm M hb f)] with x hcf hf hs hs'
    change (multiplyBoundedVectorL2 m hm M hb (c • f)) x =
      (c • multiplyBoundedVectorL2 m hm M hb f) x
    rw [hs']
    change ((boundedVectorSymbol_memLp m hm M hb (c • f)).toLp _) x =
      c • ((boundedVectorSymbol_memLp m hm M hb f).toLp _) x
    rw [hcf, hf, hs]
    exact mul_smul c (f x) (m x)

/-- The bounded multiplier as a continuous linear map. -/
def multiplyBoundedVectorL2CLM
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (multiplyBoundedVectorL2Linear m hm M hb).mkContinuous M
    (by
      intro f
      change ‖multiplyBoundedVectorL2 m hm M hb f‖ ≤ (M : ℝ) * ‖f‖
      exact norm_multiplyBoundedVectorL2_le m hm M hb f)

theorem opNNNorm_multiplyBoundedVectorL2CLM_le
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    ‖multiplyBoundedVectorL2CLM m hm M hb‖₊ ≤ M := by
  apply ContinuousLinearMap.opNNNorm_le_bound
  intro f
  change ‖multiplyBoundedVectorL2 m hm M hb f‖₊ ≤ M * ‖f‖₊
  exact_mod_cast norm_multiplyBoundedVectorL2_le m hm M hb f

/-- The Fourier multiplier as a bounded complex linear operator on `L²`. -/
def boundedVectorMultiplierL2CLM
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  let F := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ
  let G := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ ι)
  G.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((multiplyBoundedVectorL2CLM m hm M hb).comp F.toContinuousLinearEquiv.toContinuousLinearMap)

theorem norm_boundedVectorMultiplierL2CLM_apply_le
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ))
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖boundedVectorMultiplierL2CLM m hm M hb f‖ ≤ (M : ℝ) * ‖f‖ := by
  change ‖(Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ ι)).symm
    (multiplyBoundedVectorL2 m hm M hb (𝓕 f))‖ ≤ (M : ℝ) * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  simpa only [Lp.norm_fourier_eq] using norm_multiplyBoundedVectorL2_le m hm M hb (𝓕 f)

theorem opNNNorm_boundedVectorMultiplierL2CLM_le
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι) (hm : Measurable m)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    ‖boundedVectorMultiplierL2CLM m hm M hb‖₊ ≤ M := by
  apply ContinuousLinearMap.opNNNorm_le_bound
  intro f
  exact_mod_cast norm_boundedVectorMultiplierL2CLM_apply_le m hm M hb f

end PartialBalayage.Linear
