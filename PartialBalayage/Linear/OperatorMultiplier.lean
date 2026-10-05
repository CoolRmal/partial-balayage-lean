/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic

/-!
# Bounded operator-valued Fourier multipliers

An almost everywhere strongly measurable family of bounded complex linear maps acts pointwise on
the actual `L²` space. A uniform symbol bound proves boundedness of this operator. Fourier
conjugation gives a continuous linear map between arbitrary complete complex Hilbert-valued `L²`
spaces. Strong measurability avoids a separability restriction on the Hilbert spaces.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

section Pointwise

variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace ℂ E] [NormedSpace ℂ F] {μ : Measure X}

/-- A strongly measurable uniformly bounded operator symbol preserves square integrability. -/
theorem operatorSymbol_memLp (m : X → E →L[ℂ] F) (hm : AEStronglyMeasurable m μ)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) (f : Lp E 2 μ) :
    MemLp (fun x ↦ m x (f x)) 2 μ := by
  apply ((Lp.memLp f).const_smul (M : ℂ)).of_le
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hm
      (Lp.aestronglyMeasurable f))
  filter_upwards with x
  change ‖m x (f x)‖ ≤ ‖(M : ℂ) • f x‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg M.coe_nonneg]
  exact ((m x).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

/-- Pointwise application of a bounded operator symbol to an `L²` function. -/
def multiplyOperatorL2 (m : X → E →L[ℂ] F) (hm : AEStronglyMeasurable m μ)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) (f : Lp E 2 μ) : Lp F 2 μ :=
  (operatorSymbol_memLp m hm M hb f).toLp (fun x ↦ m x (f x))

/-- The `L²` representative agrees almost everywhere with pointwise symbol application. -/
theorem multiplyOperatorL2_ae (m : X → E →L[ℂ] F) (hm : AEStronglyMeasurable m μ)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) (f : Lp E 2 μ) :
    ∀ᵐ x ∂μ, multiplyOperatorL2 m hm M hb f x = m x (f x) :=
  (operatorSymbol_memLp m hm M hb f).coeFn_toLp

/-- The pointwise symbol bound is the `L²` operator bound. -/
theorem norm_multiplyOperatorL2_le (m : X → E →L[ℂ] F)
    (hm : AEStronglyMeasurable m μ) (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ))
    (f : Lp E 2 μ) : ‖multiplyOperatorL2 m hm M hb f‖ ≤ (M : ℝ) * ‖f‖ := by
  have hbound : ‖multiplyOperatorL2 m hm M hb f‖ ≤ ‖(M : ℂ) • f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [multiplyOperatorL2_ae m hm M hb f, Lp.coeFn_smul (M : ℂ) f]
      with x hx hs
    rw [hx, hs]
    change ‖m x (f x)‖ ≤ ‖(M : ℂ) • f x‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg M.coe_nonneg]
    exact ((m x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg M.coe_nonneg] using hbound

/-- Pointwise symbol application is complex linear on `L²`. -/
def multiplyOperatorL2Linear (m : X → E →L[ℂ] F) (hm : AEStronglyMeasurable m μ)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) : Lp E 2 μ →ₗ[ℂ] Lp F 2 μ where
  toFun := multiplyOperatorL2 m hm M hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [multiplyOperatorL2_ae m hm M hb (f + g),
      multiplyOperatorL2_ae m hm M hb f, multiplyOperatorL2_ae m hm M hb g,
      Lp.coeFn_add f g, Lp.coeFn_add (multiplyOperatorL2 m hm M hb f)
        (multiplyOperatorL2 m hm M hb g)] with x hfg hf hg hsum hsum'
    simp only [Pi.add_apply] at hsum hsum'
    rw [hsum', hfg, hf, hg, hsum]
    exact (m x).map_add _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [multiplyOperatorL2_ae m hm M hb (c • f),
      multiplyOperatorL2_ae m hm M hb f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (multiplyOperatorL2 m hm M hb f)] with x hcf hf hs hs'
    change multiplyOperatorL2 m hm M hb (c • f) x = (c • multiplyOperatorL2 m hm M hb f) x
    simp only [Pi.smul_apply] at hs hs'
    rw [hs', hcf, hf, hs]
    exact (m x).map_smul c _

/-- The bounded pointwise multiplication operator between actual `L²` spaces. -/
def multiplyOperatorL2CLM (m : X → E →L[ℂ] F) (hm : AEStronglyMeasurable m μ)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) : Lp E 2 μ →L[ℂ] Lp F 2 μ :=
  (multiplyOperatorL2Linear m hm M hb).mkContinuous M
    (by
      intro f
      change ‖multiplyOperatorL2 m hm M hb f‖ ≤ (M : ℝ) * ‖f‖
      exact norm_multiplyOperatorL2_le m hm M hb f)

/-- Multiplication by a uniformly bounded symbol has operator norm at most the bound. -/
theorem opNNNorm_multiplyOperatorL2CLM_le (m : X → E →L[ℂ] F)
    (hm : AEStronglyMeasurable m μ) (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    ‖multiplyOperatorL2CLM m hm M hb‖₊ ≤ M := by
  apply ContinuousLinearMap.opNNNorm_le_bound
  intro f
  change ‖multiplyOperatorL2 m hm M hb f‖₊ ≤ M * ‖f‖₊
  exact_mod_cast norm_multiplyOperatorL2_le m hm M hb f

/-- A pointwise identity component acts as the same identity component on `L²`. -/
theorem multiplyOperatorL2_eq_const_smul_add (m q : X → E →L[ℂ] E)
    (hm : AEStronglyMeasurable m μ) (hq : AEStronglyMeasurable q μ)
    (M N : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) (hqb : ∀ x, ‖q x‖ ≤ (N : ℝ))
    (c : ℂ) (heq : ∀ x, m x = c • ContinuousLinearMap.id ℂ E + q x) (f : Lp E 2 μ) :
    multiplyOperatorL2 m hm M hb f = c • f + multiplyOperatorL2 q hq N hqb f := by
  apply Lp.ext
  filter_upwards [multiplyOperatorL2_ae m hm M hb f, multiplyOperatorL2_ae q hq N hqb f,
    Lp.coeFn_add (c • f) (multiplyOperatorL2 q hq N hqb f), Lp.coeFn_smul c f]
    with x hmf hqf hadd hc
  simp only [Pi.add_apply, Pi.smul_apply] at hadd hc
  rw [hadd, hmf, hqf, hc, heq]
  rfl

end Pointwise

section Fourier

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

/-- The operator-valued Fourier multiplier as a bounded complex linear map on `L²`. -/
def operatorMultiplierL2CLM (m : EuclideanSpace ℝ (Fin n) → E →L[ℂ] F)
    (hm : AEStronglyMeasurable m volume) (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    Lp E 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  let A := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) E
  let B := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F
  B.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((multiplyOperatorL2CLM m hm M hb).comp A.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Fourier transformation converts the multiplier into pointwise multiplication in `L²`. -/
theorem fourier_operatorMultiplierL2CLM (m : EuclideanSpace ℝ (Fin n) → E →L[ℂ] F)
    (hm : AEStronglyMeasurable m volume) (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ))
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    𝓕 (operatorMultiplierL2CLM m hm M hb f) = multiplyOperatorL2 m hm M hb (𝓕 f) := by
  change (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F)
    ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F).symm
      (multiplyOperatorL2 m hm M hb (𝓕 f))) = _
  exact (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F).apply_symm_apply _

/-- Plancherel transports the symbol bound to the Fourier multiplier. -/
theorem norm_operatorMultiplierL2CLM_apply_le
    (m : EuclideanSpace ℝ (Fin n) → E →L[ℂ] F) (hm : AEStronglyMeasurable m volume)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ))
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖operatorMultiplierL2CLM m hm M hb f‖ ≤ (M : ℝ) * ‖f‖ := by
  change ‖(Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F).symm
    (multiplyOperatorL2 m hm M hb (𝓕 f))‖ ≤ (M : ℝ) * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  simpa only [Lp.norm_fourier_eq] using norm_multiplyOperatorL2_le m hm M hb (𝓕 f)

/-- The genuine Fourier multiplier has operator norm at most the uniform symbol bound. -/
theorem opNNNorm_operatorMultiplierL2CLM_le
    (m : EuclideanSpace ℝ (Fin n) → E →L[ℂ] F) (hm : AEStronglyMeasurable m volume)
    (M : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) :
    ‖operatorMultiplierL2CLM m hm M hb‖₊ ≤ M := by
  apply ContinuousLinearMap.opNNNorm_le_bound
  intro f
  exact_mod_cast norm_operatorMultiplierL2CLM_apply_le m hm M hb f

/-- Fourier conjugation preserves the explicit identity-component decomposition. -/
theorem operatorMultiplierL2CLM_eq_const_smul_add
    (m q : EuclideanSpace ℝ (Fin n) → E →L[ℂ] E)
    (hm : AEStronglyMeasurable m volume) (hq : AEStronglyMeasurable q volume)
    (M N : ℝ≥0) (hb : ∀ x, ‖m x‖ ≤ (M : ℝ)) (hqb : ∀ x, ‖q x‖ ≤ (N : ℝ))
    (c : ℂ) (heq : ∀ x, m x = c • ContinuousLinearMap.id ℂ E + q x) :
    operatorMultiplierL2CLM m hm M hb =
      c • ContinuousLinearMap.id ℂ _ + operatorMultiplierL2CLM q hq N hqb := by
  apply ContinuousLinearMap.ext
  intro f
  let A := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) E
  change A.symm (multiplyOperatorL2 m hm M hb (A f)) =
    c • f + A.symm (multiplyOperatorL2 q hq N hqb (A f))
  rw [multiplyOperatorL2_eq_const_smul_add m q hm hq M N hb hqb c heq,
    A.symm.map_add, A.symm.map_smul, A.symm_apply_apply]

end Fourier

end PartialBalayage.Linear
