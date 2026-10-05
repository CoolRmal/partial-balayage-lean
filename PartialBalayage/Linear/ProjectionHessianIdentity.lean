/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ProjectionMultiplier
public import PartialBalayage.Linear.HessianDerivative

/-!
# Genuine projection operators as coordinatewise Hessian combinations

The actual gradient projection is the negative row sum of the scalar Hessian operators
applied to the corresponding coordinates of its vector input. The Leray projection and
both shifted projections inherit exact component formulas. These are actual `L²` operator
identities, including the totalized zero-frequency symbols.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform InnerProductSpace

namespace PartialBalayage.Linear

variable {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ (Fin d)
local notation "VectorL2" => Lp V 2 (volume : Measure X)
local notation "ScalarL2" => Lp ℂ 2 (volume : Measure X)

/-- A genuine bounded complex coordinate map on the vector output space. -/
def projectionCoordinateCLM (j : Fin d) : V →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : Fin d ↦ ℂ) j

/-- The genuine scalar output coordinate agrees with the actual vector value a.e. -/
theorem projectionCoordinateCLM_ae (f : VectorL2) (j : Fin d) :
    (projectionCoordinateCLM j).compLp f =ᵐ[volume] fun x ↦ f x j :=
  (projectionCoordinateCLM j).coeFn_compLp f

/-- The actual gradient frequency symbol is the negative row sum of scalar Hessian symbols. -/
theorem gradientProjectionSymbol_apply_eq_neg_sum_hessian
    (ξ : X) (v : V) (i : Fin d) :
    gradientProjectionSymbol ξ v i = -∑ j : Fin d, hessianSymbol ξ (i, j) * v j := by
  simp only [gradientProjectionSymbol, smul_apply, rankOne_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, complexifyEuclidean,
    RCLike.inner_apply', Complex.conj_ofReal, hessianSymbol_apply, Complex.ofReal_pow]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Fourier transformation commutes with reading the actual vector input coordinate. -/
theorem fourier_projectionCoordinate_ae (f : VectorL2) (j : Fin d) :
    (𝓕 ((projectionCoordinateCLM j).compLp f) : ScalarL2) =ᵐ[volume]
      fun ξ ↦ (𝓕 f : VectorL2) ξ j := by
  rw [fourier_compLp]
  exact (projectionCoordinateCLM j).coeFn_compLp (𝓕 f)

/-- The actual gradient projection coordinate has the genuine frequency symbol. -/
theorem fourier_gradientProjectionCoordinate_ae (f : VectorL2) (i : Fin d) :
    (𝓕 ((projectionCoordinateCLM i).compLp (gradientProjectionL2CLM f)) : ScalarL2) =ᵐ[volume]
      fun ξ ↦ gradientProjectionSymbol ξ ((𝓕 f : VectorL2) ξ) i := by
  rw [fourier_compLp]
  have hF : (𝓕 (gradientProjectionL2CLM f) : VectorL2) =
      multiplyOperatorL2 gradientProjectionSymbol
        measurable_gradientProjectionSymbol.aestronglyMeasurable 1
          norm_gradientProjectionSymbol_le (𝓕 f) :=
    fourier_operatorMultiplierL2CLM gradientProjectionSymbol
      measurable_gradientProjectionSymbol.aestronglyMeasurable 1
        norm_gradientProjectionSymbol_le f
  rw [hF]
  filter_upwards [(projectionCoordinateCLM i).coeFn_compLp
    (multiplyOperatorL2 gradientProjectionSymbol
      measurable_gradientProjectionSymbol.aestronglyMeasurable 1
        norm_gradientProjectionSymbol_le (𝓕 f)),
    multiplyOperatorL2_ae gradientProjectionSymbol
      measurable_gradientProjectionSymbol.aestronglyMeasurable 1
        norm_gradientProjectionSymbol_le (𝓕 f)] with ξ hc hm
  rw [hc, hm]
  rfl

/-- Each genuine gradient projection output is the negative sum of actual scalar Hessian entries. -/
theorem gradientProjectionL2_coordinate_eq_neg_sum_hessian (f : VectorL2) (i : Fin d) :
    (projectionCoordinateCLM i).compLp (gradientProjectionL2CLM f) =
      -∑ j : Fin d, (hessianEntryCLM i j).compLp
        (hessianL2 ((projectionCoordinateCLM j).compLp f)) := by
  apply (Lp.fourierTransformₗᵢ X ℂ).injective
  change (𝓕 ((projectionCoordinateCLM i).compLp (gradientProjectionL2CLM f)) : ScalarL2) =
    𝓕 (-∑ j : Fin d, (hessianEntryCLM i j).compLp
      (hessianL2 ((projectionCoordinateCLM j).compLp f)))
  rw [FourierTransform.fourier_neg, FourierTransform.fourier_sum]
  apply Lp.ext
  filter_upwards [fourier_gradientProjectionCoordinate_ae f i,
    Lp.coeFn_neg (∑ j : Fin d, 𝓕 ((hessianEntryCLM i j).compLp
      (hessianL2 ((projectionCoordinateCLM j).compLp f)))),
    Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin d ↦
      𝓕 ((hessianEntryCLM i j).compLp (hessianL2 ((projectionCoordinateCLM j).compLp f)))),
    (ae_all_iff.mpr (fun j : Fin d ↦
      fourier_hessianEntry_ae ((projectionCoordinateCLM j).compLp f) i j)),
    (ae_all_iff.mpr (fun j : Fin d ↦ fourier_projectionCoordinate_ae f j))]
      with ξ hp hn hs hh hc
  rw [hp, hn, Pi.neg_apply, hs]
  change gradientProjectionSymbol ξ ((𝓕 f : VectorL2) ξ) i =
    -∑ j : Fin d, (𝓕 ((hessianEntryCLM i j).compLp
      (hessianL2 ((projectionCoordinateCLM j).compLp f))) : ScalarL2) ξ
  rw [gradientProjectionSymbol_apply_eq_neg_sum_hessian]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hh j, hc j, hessianSymbol_apply]
  ring

/-- The genuine Leray operator is the identity minus the genuine gradient projection. -/
theorem lerayProjectionL2CLM_eq_sub_gradient :
    lerayProjectionL2CLM (n := d) = ContinuousLinearMap.id ℂ VectorL2 -
      gradientProjectionL2CLM := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ X V).injective
  change (𝓕 (lerayProjectionL2CLM f) : VectorL2) = 𝓕 (f - gradientProjectionL2CLM f)
  have hsub : (𝓕 (f - gradientProjectionL2CLM f) : VectorL2) =
      𝓕 f - 𝓕 (gradientProjectionL2CLM f) :=
    (Lp.fourierTransformₗᵢ X V).map_sub f (gradientProjectionL2CLM f)
  rw [hsub]
  have hL : (𝓕 (lerayProjectionL2CLM f) : VectorL2) =
      multiplyOperatorL2 lerayProjectionSymbol
        measurable_lerayProjectionSymbol.aestronglyMeasurable 1
          norm_lerayProjectionSymbol_le (𝓕 f) :=
    fourier_operatorMultiplierL2CLM lerayProjectionSymbol
      measurable_lerayProjectionSymbol.aestronglyMeasurable 1 norm_lerayProjectionSymbol_le f
  have hG : (𝓕 (gradientProjectionL2CLM f) : VectorL2) =
      multiplyOperatorL2 gradientProjectionSymbol
        measurable_gradientProjectionSymbol.aestronglyMeasurable 1
          norm_gradientProjectionSymbol_le (𝓕 f) :=
    fourier_operatorMultiplierL2CLM gradientProjectionSymbol
      measurable_gradientProjectionSymbol.aestronglyMeasurable 1 norm_gradientProjectionSymbol_le f
  rw [hL, hG]
  apply Lp.ext
  filter_upwards [multiplyOperatorL2_ae lerayProjectionSymbol
    measurable_lerayProjectionSymbol.aestronglyMeasurable 1 norm_lerayProjectionSymbol_le (𝓕 f),
    multiplyOperatorL2_ae gradientProjectionSymbol
      measurable_gradientProjectionSymbol.aestronglyMeasurable 1 norm_gradientProjectionSymbol_le
        (𝓕 f),
    Lp.coeFn_sub (𝓕 f) (multiplyOperatorL2 gradientProjectionSymbol
      measurable_gradientProjectionSymbol.aestronglyMeasurable 1 norm_gradientProjectionSymbol_le
        (𝓕 f))] with ξ hL hG hs
  rw [hs, Pi.sub_apply, hL, hG]
  rfl

/-- Each actual Leray output is its input coordinate plus the Hessian row sum. -/
theorem lerayProjectionL2_coordinate_eq_add_sum_hessian (f : VectorL2) (i : Fin d) :
    (projectionCoordinateCLM i).compLp (lerayProjectionL2CLM f) =
      (projectionCoordinateCLM i).compLp f +
        ∑ j : Fin d, (hessianEntryCLM i j).compLp
          (hessianL2 ((projectionCoordinateCLM j).compLp f)) := by
  change (projectionCoordinateCLM i).compLpL 2 volume (lerayProjectionL2CLM f) = _
  rw [lerayProjectionL2CLM_eq_sub_gradient, sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  change (projectionCoordinateCLM i).compLp f -
    (projectionCoordinateCLM i).compLp (gradientProjectionL2CLM f) = _
  rw [gradientProjectionL2_coordinate_eq_neg_sum_hessian]
  module

/-- The shifted gradient output is negative half its input minus the Hessian row sum. -/
theorem shiftedGradientProjectionL2_coordinate_eq_neg_half_sub_sum_hessian
    (f : VectorL2) (i : Fin d) :
    (projectionCoordinateCLM i).compLp (shiftedGradientProjectionL2CLM f) =
      -(1 / 2 : ℂ) • (projectionCoordinateCLM i).compLp f -
        ∑ j : Fin d, (hessianEntryCLM i j).compLp
          (hessianL2 ((projectionCoordinateCLM j).compLp f)) := by
  change (projectionCoordinateCLM i).compLpL 2 volume
    (shiftedGradientProjectionL2CLM f) = _
  rw [shiftedGradientProjectionL2CLM_eq_sub_half, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul]
  change (projectionCoordinateCLM i).compLp (gradientProjectionL2CLM f) -
    (1 / 2 : ℂ) • (projectionCoordinateCLM i).compLp f = _
  rw [gradientProjectionL2_coordinate_eq_neg_sum_hessian]
  module

/-- The shifted Leray output is half its input coordinate plus the Hessian row sum. -/
theorem shiftedLerayProjectionL2_coordinate_eq_half_add_sum_hessian
    (f : VectorL2) (i : Fin d) :
    (projectionCoordinateCLM i).compLp (shiftedLerayProjectionL2CLM f) =
      (1 / 2 : ℂ) • (projectionCoordinateCLM i).compLp f +
        ∑ j : Fin d, (hessianEntryCLM i j).compLp
          (hessianL2 ((projectionCoordinateCLM j).compLp f)) := by
  change (projectionCoordinateCLM i).compLpL 2 volume (shiftedLerayProjectionL2CLM f) = _
  rw [shiftedLerayProjectionL2CLM_eq_sub_half, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul]
  change (projectionCoordinateCLM i).compLp (lerayProjectionL2CLM f) -
    (1 / 2 : ℂ) • (projectionCoordinateCLM i).compLp f = _
  rw [lerayProjectionL2_coordinate_eq_add_sum_hessian]
  module

end PartialBalayage.Linear
