/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WeakL1Extension
public import PartialBalayage.Linear.HessianWeakBounds
public import PartialBalayage.Linear.ProjectionWeakBounds
public import PartialBalayage.Linear.HessianLinearity

/-!
# Genuine full-L¹ weak bounds for the concrete linear Fourier operators

The actual capped balayage estimates hold on integrable square-integrable inputs.
The proved canonical extension theorem turns them into linear all-L¹ maps into a.e.
classes with the same exact coefficients. The associated weak constants therefore
satisfy the full Hessian, Beurling, traceless Hessian, gradient and Leray table bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace PartialBalayage.Linear

section Extension

variable {X E F 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- A finite nonnegative real coefficient retains its value under the genuine L¹ extension. -/
theorem isLinearWeakTypeBound_of_real_L2_level_bound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ u : Lp E 2 μ, Integrable (u : X → E) μ → ∀ α : ℝ≥0∞,
      α * μ {x | α < ‖T u x‖ₑ} ≤ ENNReal.ofReal C * ∫⁻ x, ‖u x‖ₑ ∂μ) :
    IsLinearWeakTypeBound (𝕜 := 𝕜) T (ENNReal.ofReal C) := by
  let c : ℝ≥0 := ⟨C, hC⟩
  have hc : (c : ℝ≥0∞) = ENNReal.ofReal C := ENNReal.ofReal_coe_nnreal.symm
  have hb' : ∀ u : Lp E 2 μ, Integrable (u : X → E) μ → ∀ α : ℝ≥0∞,
      α * μ {x | α < ‖T u x‖ₑ} ≤ (c : ℝ≥0∞) * ∫⁻ x, ‖u x‖ₑ ∂μ := by
    simpa only [hc] using hb
  simpa only [hc] using isLinearWeakTypeBound_of_L2_level_bound T c hb'

end Extension

variable {n : ℕ}

private theorem hessianCoefficient_nonneg (hn : 2 ≤ n) :
    0 ≤ hessianCoefficient n (hessianParameter n) := by
  have ha := hessianParameter_pos hn
  have hlt := hessianParameter_lt_sqrt hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hden : 0 < (n : ℝ) - hessianParameter n ^ 2 := by
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hnum : 0 ≤ ((n : ℝ) - 1) * hessianParameter n :=
    mul_nonneg (by linarith) ha.le
  unfold hessianCoefficient
  exact add_nonneg (by positivity) (div_nonneg hnum hden.le)

private theorem projectionCoefficient_nonneg :
    0 ≤ projectionCoefficient projectionParameter := by
  have ha := projectionParameter_mem.1
  unfold projectionCoefficient
  positivity

/-- The actual full Frobenius Hessian has the exact optimized full-L¹ weak bound. -/
theorem isLinearWeakTypeBound_hessian (hn : 2 ≤ n) :
    IsLinearWeakTypeBound (𝕜 := ℂ) (hessianL2CLM n)
      (ENNReal.ofReal (hessianCoefficient n (hessianParameter n))) := by
  apply isLinearWeakTypeBound_of_real_L2_level_bound _ _ (hessianCoefficient_nonneg hn)
  intro f hf α
  simpa only [hessianL2CLM_apply] using hessian_levelSet_bound_at_parameter hn f hf α

/-- The genuine full-L¹ Hessian weak constant has the exact table bound in every `n ≥ 2`. -/
theorem hessian_linearWeakTypeConstant_le (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianL2CLM n) ≤
      ENNReal.ofReal (hessianCoefficient n (hessianParameter n)) :=
  sInf_le (isLinearWeakTypeBound_hessian hn)

/-- The actual full planar Frobenius Hessian has coefficient `3 * sqrt 6 / 4` on all L¹ inputs. -/
theorem isLinearWeakTypeBound_hessian_two :
    IsLinearWeakTypeBound (𝕜 := ℂ) (hessianL2CLM 2)
      (ENNReal.ofReal (3 * Real.sqrt 6 / 4)) := by
  simpa only [hessianCoefficient_two] using
    isLinearWeakTypeBound_hessian (by norm_num : 2 ≤ 2)

/-- The full planar Hessian's actual all-L¹ weak constant satisfies the table bound. -/
theorem hessian_linearWeakTypeConstant_two_le :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianL2CLM 2) ≤
      ENNReal.ofReal (3 * Real.sqrt 6 / 4) :=
  sInf_le isLinearWeakTypeBound_hessian_two

/-- The genuine complex-linear planar Beurling operator. -/
def beurlingL2CLM :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) :=
  (beurlingHessianCombination.compLpL 2 volume).comp (hessianL2CLM 2)

/-- This actual bounded complex-linear map acts by the true Beurling multiplier. -/
theorem beurlingL2CLM_apply
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    beurlingL2CLM f = beurlingL2 f :=
  (beurlingL2_eq_hessian_combination f).symm

/-- The true complex-input Beurling transform has full-L¹ weak coefficient two. -/
theorem isLinearWeakTypeBound_beurling :
    IsLinearWeakTypeBound (𝕜 := ℂ) beurlingL2CLM 2 := by
  have hfull : IsLinearWeakTypeBound (𝕜 := ℂ) beurlingL2CLM (ENNReal.ofReal 2) := by
    apply isLinearWeakTypeBound_of_real_L2_level_bound _ 2 (by norm_num)
    intro f hf α
    simpa only [beurlingL2CLM_apply, ENNReal.ofReal_ofNat] using
      beurling_levelSet_bound f hf α
  simpa only [ENNReal.ofReal_ofNat] using hfull

/-- The actual complex-input Beurling weak constant is at most two on all L¹. -/
theorem beurling_linearWeakTypeConstant_le_two :
    linearWeakTypeConstant (𝕜 := ℂ) beurlingL2CLM ≤ 2 :=
  sInf_le isLinearWeakTypeBound_beurling

/-- The actual traceless Frobenius Hessian has its exact full-L¹ table coefficient. -/
theorem isLinearWeakTypeBound_tracelessHessian (hn : 2 ≤ n) :
    IsLinearWeakTypeBound (𝕜 := ℂ) (tracelessHessianL2CLM n (by omega))
      (ENNReal.ofReal (2 * Real.sqrt (1 - 1 / (n : ℝ)))) := by
  apply isLinearWeakTypeBound_of_real_L2_level_bound _ _ (by positivity)
  exact tracelessHessian_levelSet_bound hn

/-- The full-L¹ traceless Hessian weak constant has the exact dimension-dependent table bound. -/
theorem tracelessHessian_linearWeakTypeConstant_le (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (tracelessHessianL2CLM n (by omega)) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - 1 / (n : ℝ))) :=
  sInf_le (isLinearWeakTypeBound_tracelessHessian hn)

/-- The actual one-dimensional traceless Hessian is the zero bounded linear map. -/
theorem tracelessHessianL2CLM_one_eq_zero :
    tracelessHessianL2CLM 1 (by norm_num) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa using norm_tracelessHessianL2CLM_apply_le (by norm_num : 0 < 1) f

/-- The true one-dimensional traceless Hessian has full-L¹ weak coefficient zero. -/
theorem isLinearWeakTypeBound_tracelessHessian_one :
    IsLinearWeakTypeBound (𝕜 := ℂ) (tracelessHessianL2CLM 1 (by norm_num)) 0 := by
  rw [← ENNReal.ofReal_zero]
  apply isLinearWeakTypeBound_of_real_L2_level_bound _ 0 le_rfl
  intro f _ α
  rw [tracelessHessianL2CLM_one_eq_zero]
  simp only [zero_apply]
  have hs : {x | α < ‖(0 : Lp (EuclideanSpace ℂ (Fin 1 × Fin 1)) 2 volume) x‖ₑ} =ᵐ[volume]
      (∅ : Set (EuclideanSpace ℝ (Fin 1))) := by
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℂ (Fin 1 × Fin 1)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 1)))] with x hx
    simp only [hx, Pi.zero_apply, enorm_zero, not_lt_zero, Set.mem_empty_iff_false]
  rw [measure_congr hs]
  simp

/-- The one-dimensional traceless Hessian's actual all-L¹ weak constant is zero. -/
theorem tracelessHessian_linearWeakTypeConstant_one_eq_zero :
    linearWeakTypeConstant (𝕜 := ℂ) (tracelessHessianL2CLM 1 (by norm_num)) = 0 :=
  le_antisymm (sInf_le isLinearWeakTypeBound_tracelessHessian_one) zero_le

/-- The actual gradient projection has the exact cubic-root coefficient on every L¹ input. -/
theorem isLinearWeakTypeBound_gradientProjection (hn : 1 ≤ n) :
    IsLinearWeakTypeBound (𝕜 := ℂ) (gradientProjectionL2CLM (n := n))
      (ENNReal.ofReal (projectionCoefficient projectionParameter)) := by
  apply isLinearWeakTypeBound_of_real_L2_level_bound _ _ projectionCoefficient_nonneg
  exact gradientProjection_levelSet_bound hn

/-- The gradient projection's genuine all-L¹ weak constant has the exact table bound. -/
theorem gradientProjection_linearWeakTypeConstant_le (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (gradientProjectionL2CLM (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) :=
  sInf_le (isLinearWeakTypeBound_gradientProjection hn)

/-- The actual Leray projection has the same exact cubic-root coefficient on every L¹ input. -/
theorem isLinearWeakTypeBound_lerayProjection (hn : 1 ≤ n) :
    IsLinearWeakTypeBound (𝕜 := ℂ) (lerayProjectionL2CLM (n := n))
      (ENNReal.ofReal (projectionCoefficient projectionParameter)) := by
  apply isLinearWeakTypeBound_of_real_L2_level_bound _ _ projectionCoefficient_nonneg
  exact lerayProjection_levelSet_bound hn

/-- The Leray projection's genuine all-L¹ weak constant has the exact table bound. -/
theorem lerayProjection_linearWeakTypeConstant_le (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (lerayProjectionL2CLM (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) :=
  sInf_le (isLinearWeakTypeBound_lerayProjection hn)

end PartialBalayage.Linear
