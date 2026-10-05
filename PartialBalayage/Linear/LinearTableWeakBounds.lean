/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LinearWeakBounds
public import PartialBalayage.Linear.FourierOperatorBridge

/-!
# Full-L¹ table bounds for the independently defined Fourier operators

The independent concrete Fourier definitions equal the actual bounded multipliers.
The genuine all-L¹ linear extensions and exact capped-balayage bounds therefore
prove the article's five Hessian, Beurling and projection rows in their full scope.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PartialBalayage.Linear

/-- The full Frobenius Hessian's exact all-L¹ bound in every dimension at least two. -/
theorem hessian_weakTypeConstant_le_formula (n : ℕ) (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianFourierOperator (n := n)) ≤
      ENNReal.ofReal (hessianCoefficient n (hessianParameter n)) := by
  have heq : (hessianFourierOperator (n := n)) = (hessianL2CLM n) := by
    funext f
    exact (hessianFourierOperator_eq_hessianL2 f).trans (hessianL2CLM_apply f).symm
  rw [heq]
  exact hessian_linearWeakTypeConstant_le hn

/-- The full planar Frobenius Hessian's exact coefficient is `3 * sqrt 6 / 4`. -/
theorem hessian_weakTypeConstant_two_le_exact :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianFourierOperator (n := 2)) ≤
      ENNReal.ofReal (3 * Real.sqrt 6 / 4) := by
  simpa only [hessianCoefficient_two] using hessian_weakTypeConstant_le_formula 2 (by norm_num)

/-- The actual complex-input Beurling transform has all-L¹ weak coefficient at most two. -/
theorem beurling_weakTypeConstant_le_two :
    linearWeakTypeConstant (𝕜 := ℂ) beurlingFourierOperator ≤ 2 := by
  have heq : beurlingFourierOperator = beurlingL2CLM := by
    funext f
    exact (beurlingFourierOperator_eq_beurlingL2 f).trans (beurlingL2CLM_apply f).symm
  rw [heq]
  exact beurling_linearWeakTypeConstant_le_two

/-- The full traceless Frobenius Hessian has the dimension-dependent table coefficient. -/
theorem tracelessHessian_weakTypeConstant_le (n : ℕ) (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (tracelessHessianFourierOperator (n := n)) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - 1 / (n : ℝ))) := by
  have heq : (tracelessHessianFourierOperator (n := n)) =
      (tracelessHessianL2CLM n (by omega)) := by
    funext f
    exact tracelessHessianFourierOperator_eq_tracelessHessianL2CLM (by omega) f
  rw [heq]
  by_cases hn1 : n = 1
  · subst n
    rw [tracelessHessian_linearWeakTypeConstant_one_eq_zero]
    exact zero_le
  · exact tracelessHessian_linearWeakTypeConstant_le (by omega)

/-- Both actual projections have the same exact cubic-root coefficient on all L¹ inputs. -/
theorem projections_weakTypeConstants_le_exact (n : ℕ) (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (gradientFourierOperator (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) ∧
    linearWeakTypeConstant (𝕜 := ℂ) (lerayFourierOperator (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) := by
  have hG : (gradientFourierOperator (n := n)) = (gradientProjectionL2CLM (n := n)) := by
    funext f
    exact gradientFourierOperator_eq_gradientProjectionL2CLM f
  have hL : (lerayFourierOperator (n := n)) = (lerayProjectionL2CLM (n := n)) := by
    funext f
    exact lerayFourierOperator_eq_lerayProjectionL2CLM f
  rw [hG, hL]
  exact ⟨gradientProjection_linearWeakTypeConstant_le (by omega),
    lerayProjection_linearWeakTypeConstant_le (by omega)⟩

end PartialBalayage.Linear
