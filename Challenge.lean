/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Challenge.MaximalDefinitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Auditable statements: nine completed table bounds

The published source is Yongxi Lin's "Two partial balayage principles for weak-type estimates".
This statement surface covers centred intervals, Euclidean balls, and all six heat and Poisson
maximal bounds. Seven rows remain unproved and are tracked in `docs/DECOMPOSITION.md`.
The source's decimal approximations will not be substituted for its exact bounds.

The interval domain `Fin 1 → ℝ` is the standard real line in one coordinate. Cubes use the sup
norm; balls use the Euclidean norm. All inputs are integrable and all levels are quantified.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace PartialBalayage

/-- The standard Poisson kernel on Euclidean `n`-space at height `t > 0`. -/
def poissonKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) *
    t / (t ^ 2 + ‖x‖ ^ 2) ^ (((n : ℝ) + 1) / 2)

/-- The standard heat kernel at time `t > 0`, with generator `Δ`. -/
def heatKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- The Poisson maximal function is the supremum over all positive heights of `p_t * |f|`. -/
def poissonMaximalFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), ∫⁻ y, ENNReal.ofReal (poissonKernel n t (x - y)) * ‖f y‖ₑ

/-- The heat maximal function is the supremum over all positive times of `h_t * |f|`. -/
def heatMaximalFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), ∫⁻ y, ENNReal.ofReal (heatKernel n t (x - y)) * ‖f y‖ₑ

/-- A weak type `(1,1)` bound for the Poisson maximal operator for all integrable real inputs. -/
def IsPoissonWeakTypeBound (n : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < poissonMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- A weak type `(1,1)` bound for the heat maximal operator for all integrable real inputs. -/
def IsHeatWeakTypeBound (n : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < heatMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The least weak type `(1,1)` bound for the Poisson maximal operator. -/
def poissonWeakTypeConstant (n : ℕ) : ℝ≥0∞ := sInf {C | IsPoissonWeakTypeBound n C}

/-- The least weak type `(1,1)` bound for the heat maximal operator. -/
def heatWeakTypeConstant (n : ℕ) : ℝ≥0∞ := sInf {C | IsHeatWeakTypeBound n C}

/-- The article's exact Poisson bound formula, before choosing its tangency parameters. -/
def poissonBoundFormula (n : ℕ) (a b : ℝ) : ℝ :=
  Real.Gamma (((n : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((n : ℝ) / 2)) *
    (2 * b ^ ((n : ℝ) / 2) / ((n : ℝ) * (1 + a) ^ (((n : ℝ) + 1) / 2)) +
      ∫ z in Set.Ioi b, z ^ ((n : ℝ) / 2 - 1) / (1 + z) ^ (((n : ℝ) + 1) / 2))

/-- The article's exact heat bound formula, before choosing its tangency parameters. -/
def heatBoundFormula (n : ℕ) (a b : ℝ) : ℝ :=
  (Real.Gamma ((n : ℝ) / 2))⁻¹ *
    (2 * b ^ ((n : ℝ) / 2) * Real.exp (-a) / (n : ℝ) +
      ∫ z in Set.Ioi b, z ^ ((n : ℝ) / 2 - 1) * Real.exp (-z))

/-- The one-dimensional Poisson row's exact constant, rather than its rounded approximation. -/
def poissonOneBound : ℝ :=
  1 + 2 / Real.pi * (Real.sqrt 5 / 3 - Real.arctan (2 / Real.sqrt 5))

namespace Constants

/-- The article's exact squared-radius joining ratio. -/
def rho (n : ℕ) : ℝ :=
  if n = 2 then Real.exp 1 else ((n : ℝ) / 2) ^ (2 / ((n : ℝ) - 2))

end Constants

open Constants

def IsHeatTangencyParameter (n : ℕ) (a : ℝ) : Prop :=
  a ∈ Ioo ((n : ℝ) / (2 * rho n)) ((n : ℝ) / 2) ∧
    Real.exp (-(rho n - 1) * a) = 1 - 2 * a / (n : ℝ)

def IsPoissonTangencyParameter (n : ℕ) (a : ℝ) : Prop :=
  a ∈ Ioo ((n : ℝ) / (3 * rho n)) ((n : ℝ) / 3) ∧
    (1 - a / (n : ℝ)) / (1 + a) ^ (((n : ℝ) + 3) / 2) =
      1 / (1 + rho n * a) ^ (((n : ℝ) + 1) / 2)

def heatTangencyParameter (n : ℕ) : ℝ := Classical.epsilon (IsHeatTangencyParameter n)

def poissonTangencyParameter (n : ℕ) : ℝ := Classical.epsilon (IsPoissonTangencyParameter n)

def complementaryErrorFunction (r : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ s in Set.Ioi r, Real.exp (-(s ^ 2))

/-- The table's interval bound: the centred weak type `(1,1)` constant is at most `2`. -/
theorem interval_weakTypeConstant_le_two : cubeWeakTypeConstant 1 ≤ 2 := by
  sorry

/-- The table's planar Euclidean-ball bound: the centred weak type constant is at most `e`. -/
theorem ball_weakTypeConstant_two_le_exp :
    ballWeakTypeConstant 2 ≤ ENNReal.ofReal (Real.exp 1) := by
  sorry

/-- The table's Euclidean-ball bound in every dimension `n ≥ 3`. -/
theorem ball_weakTypeConstant_le_rpow (n : ℕ) (hn : 3 ≤ n) :
    ballWeakTypeConstant n ≤
      ENNReal.ofReal (((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))) := by
  sorry
/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    heatWeakTypeConstant n ≤ ENNReal.ofReal
      (heatBoundFormula n (heatTangencyParameter n) (rho n * heatTangencyParameter n)) := by
  sorry

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    poissonWeakTypeConstant n ≤ ENNReal.ofReal
      (poissonBoundFormula n (poissonTangencyParameter n)
        (rho n * poissonTangencyParameter n)) := by
  sorry

/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_two_le_exact :
    heatWeakTypeConstant 2 ≤ ENNReal.ofReal
      ((1 + (Real.exp 1 - 1) * heatTangencyParameter 2) * Real.exp (-heatTangencyParameter 2)) := by
  sorry

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_two_le_exact :
    poissonWeakTypeConstant 2 ≤ ENNReal.ofReal
      (Real.exp 1 * poissonTangencyParameter 2 /
        (2 * (1 + poissonTangencyParameter 2) ^ (3 / 2 : ℝ)) +
          1 / (1 + Real.exp 1 * poissonTangencyParameter 2) ^ (1 / 2 : ℝ)) := by
  sorry

/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_one_le_exact :
    heatWeakTypeConstant 1 ≤ ENNReal.ofReal
      (4 * Real.sqrt (heatTangencyParameter 1 / Real.pi) * Real.exp (-heatTangencyParameter 1) +
        complementaryErrorFunction (2 * Real.sqrt (heatTangencyParameter 1))) := by
  sorry

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_one_le_exact :
    poissonWeakTypeConstant 1 ≤ ENNReal.ofReal poissonOneBound := by
  sorry

end PartialBalayage
