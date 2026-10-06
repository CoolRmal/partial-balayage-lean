/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage

/-!
# Implementations of the currently advertised statements

Comparator checks this module independently against `Challenge.lean`.
No unproved row of the article is represented by a conditional substitute here.
-/

@[expose] public section

open scoped ENNReal
open PartialBalayage.Constants

namespace PartialBalayage

/-- The centred interval weak type `(1,1)` constant is at most `2`. -/
theorem interval_weakTypeConstant_le_two : cubeWeakTypeConstant 1 ≤ 2 :=
  Maximal.interval_weakTypeConstant_le_two

/-- The centred planar Euclidean-ball weak type constant is at most `e`. -/
theorem ball_weakTypeConstant_two_le_exp :
    ballWeakTypeConstant 2 ≤ ENNReal.ofReal (Real.exp 1) :=
  Maximal.ball_weakTypeConstant_two_le_exp

/-- The centred Euclidean-ball weak type bound in dimensions `n ≥ 3`. -/
theorem ball_weakTypeConstant_le_rpow (n : ℕ) (hn : 3 ≤ n) :
    ballWeakTypeConstant n ≤
      ENNReal.ofReal (((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))) :=
  Maximal.ball_weakTypeConstant_le_rpow n hn
/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    heatWeakTypeConstant n ≤ ENNReal.ofReal
      (heatBoundFormula n (heatTangencyParameter n) (rho n * heatTangencyParameter n)) :=
  Maximal.heat_weakTypeConstant_le_formula n hn

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    poissonWeakTypeConstant n ≤ ENNReal.ofReal
      (poissonBoundFormula n (poissonTangencyParameter n) (rho n * poissonTangencyParameter n)) :=
  Maximal.poisson_weakTypeConstant_le_formula n hn

/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_two_le_exact :
    heatWeakTypeConstant 2 ≤ ENNReal.ofReal
      ((1 + (Real.exp 1 - 1) * heatTangencyParameter 2) * Real.exp (-heatTangencyParameter 2)) :=
  Maximal.heat_weakTypeConstant_two_le_exact

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_two_le_exact :
    poissonWeakTypeConstant 2 ≤ ENNReal.ofReal
      (Real.exp 1 * poissonTangencyParameter 2 /
        (2 * (1 + poissonTangencyParameter 2) ^ (3 / 2 : ℝ)) +
          1 / (1 + Real.exp 1 * poissonTangencyParameter 2) ^ (1 / 2 : ℝ)) :=
  Maximal.poisson_weakTypeConstant_two_le_exact

/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_one_le_exact :
    heatWeakTypeConstant 1 ≤ ENNReal.ofReal
      (4 * Real.sqrt (heatTangencyParameter 1 / Real.pi) * Real.exp (-heatTangencyParameter 1) +
        complementaryErrorFunction (2 * Real.sqrt (heatTangencyParameter 1))) :=
  Maximal.heat_weakTypeConstant_one_le_exact

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_one_le_exact :
    poissonWeakTypeConstant 1 ≤ ENNReal.ofReal poissonOneBound :=
  Maximal.poisson_weakTypeConstant_one_le_exact

/-- The full Frobenius Hessian's exact all-L¹ bound in every dimension at least two. -/
theorem hessian_weakTypeConstant_le_formula (n : ℕ) (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianFourierOperator (n := n)) ≤
      ENNReal.ofReal (hessianCoefficient n (hessianParameter n)) :=
  Linear.hessian_weakTypeConstant_le_formula n hn

/-- The full planar Frobenius Hessian's exact coefficient is `3 * sqrt 6 / 4`. -/
theorem hessian_weakTypeConstant_two_le_exact :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianFourierOperator (n := 2)) ≤
      ENNReal.ofReal (3 * Real.sqrt 6 / 4) :=
  Linear.hessian_weakTypeConstant_two_le_exact

/-- The actual complex-input Beurling transform has all-L¹ weak coefficient at most two. -/
theorem beurling_weakTypeConstant_le_two :
    linearWeakTypeConstant (𝕜 := ℂ) beurlingFourierOperator ≤ 2 :=
  Linear.beurling_weakTypeConstant_le_two

/-- The full traceless Frobenius Hessian has the dimension-dependent table coefficient. -/
theorem tracelessHessian_weakTypeConstant_le (n : ℕ) (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (tracelessHessianFourierOperator (n := n)) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - 1 / (n : ℝ))) :=
  Linear.tracelessHessian_weakTypeConstant_le n hn

/-- Both actual projections have the same exact cubic-root coefficient on all L¹ inputs. -/
theorem projections_weakTypeConstants_le_exact (n : ℕ) (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (gradientFourierOperator (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) ∧
    linearWeakTypeConstant (𝕜 := ℂ) (lerayFourierOperator (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) :=
  Linear.projections_weakTypeConstants_le_exact n hn

/-- The complete complex-input Riesz vector has coefficient two on every complex L¹ input. -/
theorem riesz_weakTypeConstant_le_two (n : ℕ) (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (complexRieszFourierOperator (n := n)) ≤ 2 :=
  Linear.complex_riesz_weakTypeConstant_le_two n hn

/-- The centered square maximal operator has weak-type constant strictly below 3.616. -/
theorem square_weakTypeConstant_lt_3_616 :
    cubeWeakTypeConstant 2 < ENNReal.ofReal (452 / 125 : ℝ) :=
  Maximal.square_weakTypeConstant_lt_3_616

end PartialBalayage
