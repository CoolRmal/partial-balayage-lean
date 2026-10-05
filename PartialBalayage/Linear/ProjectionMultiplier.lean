/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.OperatorMultiplier
public import PartialBalayage.Linear.ProjectionSymbol

/-!
# Gradient and Leray projections as bounded operators on L²

The actual orthogonal projection symbols define complex linear Fourier multipliers on the
vector-valued `L²` space. Both are contractions. Each is half the identity plus a Fourier multiplier
whose operator norm is at most one half, as required by the identity-component level-set argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

/-- The gradient projection symbol with half the identity removed. -/
def shiftedGradientProjectionSymbol (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  gradientProjectionSymbol ξ - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _

/-- The Leray projection symbol with half the identity removed. -/
def shiftedLerayProjectionSymbol (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  lerayProjectionSymbol ξ - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _

/-- Subtracting a constant map preserves measurability of the gradient symbol. -/
theorem measurable_shiftedGradientProjectionSymbol :
    Measurable (shiftedGradientProjectionSymbol (n := n)) :=
  measurable_gradientProjectionSymbol.sub measurable_const

/-- Subtracting a constant map preserves measurability of the Leray symbol. -/
theorem measurable_shiftedLerayProjectionSymbol :
    Measurable (shiftedLerayProjectionSymbol (n := n)) :=
  measurable_lerayProjectionSymbol.sub measurable_const

/-- The shifted gradient symbol has operator norm at most one half. -/
theorem norm_shiftedGradientProjectionSymbol_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖shiftedGradientProjectionSymbol ξ‖ ≤ (1 / 2 : ℝ) :=
  norm_gradientProjectionSymbol_sub_half_le ξ

/-- The shifted Leray symbol has operator norm at most one half. -/
theorem norm_shiftedLerayProjectionSymbol_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖shiftedLerayProjectionSymbol ξ‖ ≤ (1 / 2 : ℝ) :=
  norm_lerayProjectionSymbol_sub_half_le ξ

/-- The actual gradient projection as a bounded Fourier multiplier on vector-valued `L²`. -/
def gradientProjectionL2CLM :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  operatorMultiplierL2CLM gradientProjectionSymbol
    measurable_gradientProjectionSymbol.aestronglyMeasurable 1 norm_gradientProjectionSymbol_le

/-- The actual Leray projection as a bounded Fourier multiplier on vector-valued `L²`. -/
def lerayProjectionL2CLM :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  operatorMultiplierL2CLM lerayProjectionSymbol
    measurable_lerayProjectionSymbol.aestronglyMeasurable 1 norm_lerayProjectionSymbol_le

/-- The Fourier multiplier defined by the shifted gradient symbol. -/
def shiftedGradientProjectionL2CLM :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  operatorMultiplierL2CLM shiftedGradientProjectionSymbol
    measurable_shiftedGradientProjectionSymbol.aestronglyMeasurable (1 / 2)
    (fun ξ ↦ by simpa using norm_shiftedGradientProjectionSymbol_le ξ)

/-- The Fourier multiplier defined by the shifted Leray symbol. -/
def shiftedLerayProjectionL2CLM :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  operatorMultiplierL2CLM shiftedLerayProjectionSymbol
    measurable_shiftedLerayProjectionSymbol.aestronglyMeasurable (1 / 2)
    (fun ξ ↦ by simpa using norm_shiftedLerayProjectionSymbol_le ξ)

/-- The gradient projection is a contraction on the actual vector-valued `L²` space. -/
theorem opNNNorm_gradientProjectionL2CLM_le : ‖gradientProjectionL2CLM (n := n)‖₊ ≤ 1 :=
  opNNNorm_operatorMultiplierL2CLM_le gradientProjectionSymbol
    measurable_gradientProjectionSymbol.aestronglyMeasurable 1 norm_gradientProjectionSymbol_le

/-- The Leray projection is a contraction on the actual vector-valued `L²` space. -/
theorem opNNNorm_lerayProjectionL2CLM_le : ‖lerayProjectionL2CLM (n := n)‖₊ ≤ 1 :=
  opNNNorm_operatorMultiplierL2CLM_le lerayProjectionSymbol
    measurable_lerayProjectionSymbol.aestronglyMeasurable 1 norm_lerayProjectionSymbol_le

/-- The shifted gradient projection has genuine `L²` operator norm at most one half. -/
theorem opNNNorm_shiftedGradientProjectionL2CLM_le :
    ‖shiftedGradientProjectionL2CLM (n := n)‖₊ ≤ (1 / 2 : ℝ≥0) :=
  opNNNorm_operatorMultiplierL2CLM_le shiftedGradientProjectionSymbol
    measurable_shiftedGradientProjectionSymbol.aestronglyMeasurable (1 / 2)
    (fun ξ ↦ by simpa using norm_shiftedGradientProjectionSymbol_le ξ)

/-- The shifted Leray projection has genuine `L²` operator norm at most one half. -/
theorem opNNNorm_shiftedLerayProjectionL2CLM_le :
    ‖shiftedLerayProjectionL2CLM (n := n)‖₊ ≤ (1 / 2 : ℝ≥0) :=
  opNNNorm_operatorMultiplierL2CLM_le shiftedLerayProjectionSymbol
    measurable_shiftedLerayProjectionSymbol.aestronglyMeasurable (1 / 2)
    (fun ξ ↦ by simpa using norm_shiftedLerayProjectionSymbol_le ξ)

/-- The actual gradient operator is half the identity plus its bounded shifted multiplier. -/
theorem gradientProjectionL2CLM_eq_half_add :
    gradientProjectionL2CLM (n := n) =
      (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _ + shiftedGradientProjectionL2CLM := by
  apply operatorMultiplierL2CLM_eq_const_smul_add
  intro ξ
  unfold shiftedGradientProjectionSymbol
  module

/-- The actual Leray operator is half the identity plus its bounded shifted multiplier. -/
theorem lerayProjectionL2CLM_eq_half_add :
    lerayProjectionL2CLM (n := n) =
      (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _ + shiftedLerayProjectionL2CLM := by
  apply operatorMultiplierL2CLM_eq_const_smul_add
  intro ξ
  unfold shiftedLerayProjectionSymbol
  module

/-- Subtracting half the identity from the actual gradient operator gives the shifted multiplier. -/
theorem shiftedGradientProjectionL2CLM_eq_sub_half :
    shiftedGradientProjectionL2CLM (n := n) =
      gradientProjectionL2CLM - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _ := by
  rw [gradientProjectionL2CLM_eq_half_add]
  module

/-- Subtracting half the identity from the actual Leray operator gives the shifted multiplier. -/
theorem shiftedLerayProjectionL2CLM_eq_sub_half :
    shiftedLerayProjectionL2CLM (n := n) =
      lerayProjectionL2CLM - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _ := by
  rw [lerayProjectionL2CLM_eq_half_add]
  module

end PartialBalayage.Linear
