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
# Centred maximal operators in the article's table

These transparent definitions are independently repeated in `Challenge.lean`.
The domain `Fin d → ℝ` has the sup norm, whereas `EuclideanSpace ℝ (Fin d)` has the Euclidean norm.
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

end PartialBalayage
