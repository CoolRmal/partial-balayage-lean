/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Definitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Poisson and heat operators

These are the ordinary convolution maximal operators in the published table.
The parameterized exact bound formulas do not assert an inequality: constructing the
article's unique parameters and proving the operator bounds are separate outstanding tasks.
-/

@[expose] public section

noncomputable section

open MeasureTheory
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

theorem poissonKernel_pos (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < poissonKernel n t x := by
  have hΓ : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hx : 0 < t ^ 2 + ‖x‖ ^ 2 := by positivity
  unfold poissonKernel
  positivity

theorem heatKernel_pos (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < heatKernel n t x := by
  unfold heatKernel
  positivity

end PartialBalayage
