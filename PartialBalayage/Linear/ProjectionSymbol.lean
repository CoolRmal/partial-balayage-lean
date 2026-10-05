/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.RieszMultiplier
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

/-!
# The gradient and Leray projection symbols

The gradient symbol is orthogonal projection onto the real frequency direction, viewed in
complex Euclidean space. The Leray symbol is its complementary projection. Subtracting half the
identity gives half a reflection and hence an exact pointwise norm bound of one half.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}

/-- The orthogonal gradient projection symbol `ξ ξᵀ / ‖ξ‖²`. -/
def gradientProjectionSymbol (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  ((‖ξ‖ ^ (2 : ℕ) : ℝ)⁻¹ : ℂ) •
    rankOne ℂ (complexifyEuclidean ξ) (complexifyEuclidean ξ)

/-- The projection onto divergence-free frequency vectors. -/
def lerayProjectionSymbol (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  ContinuousLinearMap.id ℂ _ - gradientProjectionSymbol ξ

theorem gradientProjectionSymbol_eq_starProjection (ξ : EuclideanSpace ℝ (Fin n)) :
    gradientProjectionSymbol ξ = (ℂ ∙ complexifyEuclidean ξ).starProjection := by
  apply ContinuousLinearMap.ext
  intro v
  rw [Submodule.starProjection_singleton]
  simp only [gradientProjectionSymbol, smul_apply, rankOne_apply,
    norm_complexifyEuclidean, div_eq_mul_inv, smul_smul]
  rw [mul_comm]
  rfl

theorem measurable_gradientProjectionSymbol :
    Measurable (gradientProjectionSymbol (n := n)) := by
  have hcont : Continuous (fun ξ : EuclideanSpace ℝ (Fin n) ↦
      rankOne ℂ (complexifyEuclidean ξ) (complexifyEuclidean ξ)) := by
    simp_rw [rankOne_def]
    exact (ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin n))
      (EuclideanSpace ℂ (Fin n))).continuous₂.comp₂
        ((innerSL ℂ).continuous.comp continuous_complexifyEuclidean)
        continuous_complexifyEuclidean
  unfold gradientProjectionSymbol
  exact ((Complex.measurable_ofReal.comp (measurable_norm.pow_const 2)).inv).smul
    hcont.measurable

theorem measurable_lerayProjectionSymbol :
    Measurable (lerayProjectionSymbol (n := n)) :=
  measurable_const.sub measurable_gradientProjectionSymbol

theorem norm_gradientProjectionSymbol_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖gradientProjectionSymbol ξ‖ ≤ 1 := by
  rw [gradientProjectionSymbol_eq_starProjection]
  exact Submodule.starProjection_norm_le _

theorem lerayProjectionSymbol_eq_starProjection (ξ : EuclideanSpace ℝ (Fin n)) :
    lerayProjectionSymbol ξ = (ℂ ∙ complexifyEuclidean ξ)ᗮ.starProjection := by
  rw [lerayProjectionSymbol, gradientProjectionSymbol_eq_starProjection]
  exact (Submodule.starProjection_orthogonal _).symm

theorem norm_lerayProjectionSymbol_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖lerayProjectionSymbol ξ‖ ≤ 1 := by
  rw [lerayProjectionSymbol_eq_starProjection]
  exact Submodule.starProjection_norm_le _

/-- The shifted gradient projection is half a reflection, at every frequency. -/
theorem norm_gradientProjectionSymbol_sub_half_apply
    (ξ : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℂ (Fin n)) :
    ‖gradientProjectionSymbol ξ v - (1 / 2 : ℂ) • v‖ = (1 / 2 : ℝ) * ‖v‖ := by
  have heq : gradientProjectionSymbol ξ v - (1 / 2 : ℂ) • v =
      (1 / 2 : ℂ) • (ℂ ∙ complexifyEuclidean ξ).reflection v := by
    rw [Submodule.reflection_apply, gradientProjectionSymbol_eq_starProjection]
    module
  rw [heq, norm_smul, LinearIsometryEquiv.norm_map]
  norm_num

theorem norm_gradientProjectionSymbol_sub_half_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖gradientProjectionSymbol ξ - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _‖ ≤
      (1 / 2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound
    (gradientProjectionSymbol ξ - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _)
    (by norm_num)
  intro v
  change ‖gradientProjectionSymbol ξ v - (1 / 2 : ℂ) • v‖ ≤ (1 / 2 : ℝ) * ‖v‖
  exact (norm_gradientProjectionSymbol_sub_half_apply ξ v).le

theorem norm_lerayProjectionSymbol_sub_half_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖lerayProjectionSymbol ξ - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _‖ ≤
      (1 / 2 : ℝ) := by
  have heq : lerayProjectionSymbol ξ - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _ =
      -(gradientProjectionSymbol ξ - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _) := by
    unfold lerayProjectionSymbol
    module
  rw [heq, norm_neg]
  exact norm_gradientProjectionSymbol_sub_half_le ξ

end PartialBalayage.Linear
