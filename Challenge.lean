/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Auditable statements: first three table bounds

The published source is Yongxi Lin's "Two partial balayage principles for weak-type estimates".
This initial statement surface covers only the centred interval and Euclidean-ball bounds.
The remaining thirteen rows are unproved and are explicitly tracked in `docs/DECOMPOSITION.md`.
The source's decimal approximations will not be substituted for its exact bounds.

The interval domain `Fin 1 → ℝ` is the standard real line in one coordinate. Cubes use the sup
norm; balls use the Euclidean norm. All inputs are integrable and all levels are quantified.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace PartialBalayage

/-- The centred maximal function over axis-parallel cubes of side `2r`. -/
def cubeMaximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ

/-- `C` bounds the weak type `(1,1)` inequality for every integrable real input over cubes. -/
def IsCubeWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : (Fin d → ℝ) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < cubeMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The least weak type `(1,1)` bound for the centred cube maximal operator. -/
def cubeWeakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsCubeWeakTypeBound d C}

/-- The centred maximal function over open Euclidean balls of radius `r`. -/
def ballMaximalFunction {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ

/-- `C` bounds the weak type `(1,1)` inequality for every integrable real input over balls. -/
def IsBallWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < ballMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The least weak type `(1,1)` bound for the centred Euclidean-ball maximal operator. -/
def ballWeakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsBallWeakTypeBound d C}

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

end PartialBalayage
