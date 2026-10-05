/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiagonalIntegralBoundary
public import PartialBalayage.Maximal.Square.DiagonalIntegralDensity
public import PartialBalayage.Maximal.Square.DiagonalBetaNormalization
public import PartialBalayage.Maximal.Square.DiamondGeneratorHomogeneity
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact actual diagonal source evaluation

Ordinary fundamental theorems of calculus apply to the two actual smooth
primitive pieces. The genuine origin and infinity limits cancel, and the
positive-beta identities yield the exact intrinsic radial source constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- The genuine diagonal integral is the exact combination of convergent positive beta integrals. -/
theorem integral_diagonalWeightedDifference_eq_positiveBeta :
    (∫ t in Ioi (0 : ℝ), diagonalWeightedDifference t) =
      11 * realBetaIntegral (4 / 5) (12 / 5) -
        (7 / 2 : ℝ) * realBetaIntegral (4 / 5) (4 / 5) := by
  have hj₀ : IntervalIntegrable diagonalWeightedDifference volume (0 : ℝ) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (integrableOn_diagonalWeightedDifference.mono_set Ioc_subset_Ioi_self)
  have hp₀ : IntervalIntegrable diagonalPlusBetaDensity volume (0 : ℝ) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (integrableOn_diagonalPlusBetaDensity.mono_set Ioc_subset_Ioi_self)
  have hm₀ : IntervalIntegrable diagonalMinusBetaDensity volume (0 : ℝ) (1 / 2) := by
    apply intervalIntegrable_diagonalMinusBetaDensity.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hj₁ : IntegrableOn diagonalWeightedDifference (Ioi (1 / 2 : ℝ)) :=
    integrableOn_diagonalWeightedDifference.mono_set (Ioi_subset_Ioi (by norm_num))
  have hp₁ : IntegrableOn diagonalPlusBetaDensity (Ioi (1 / 2 : ℝ)) :=
    integrableOn_diagonalPlusBetaDensity.mono_set (Ioi_subset_Ioi (by norm_num))
  have hnearInt : IntervalIntegrable (fun t ↦ diagonalWeightedDifference t -
      11 * diagonalPlusBetaDensity t + 7 * diagonalMinusBetaDensity t)
        volume (0 : ℝ) (1 / 2) := (hj₀.sub (hp₀.const_mul 11)).add (hm₀.const_mul 7)
  have hnearDeriv : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt diagonalNearBoundary
      (diagonalWeightedDifference t - 11 * diagonalPlusBetaDensity t +
        7 * diagonalMinusBetaDensity t) t := by
    intro t ht
    have hd := hasDerivAt_diagonalNearBoundary ht.1 (by linarith [ht.2])
    simpa only [diagonalWeightedDifference, diagonalDifference, ite_eq_left ht.2.le,
      diagonalNearDifference] using hd
  have hnearHalf : Tendsto diagonalNearBoundary (𝓝[<] (1 / 2 : ℝ))
      (𝓝 (diagonalNearBoundary (1 / 2))) :=
    (hasDerivAt_diagonalNearBoundary (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hnear := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 1 / 2) hnearDeriv hnearInt
      tendsto_diagonalNearBoundary_zero hnearHalf
  rw [intervalIntegral.integral_add (hj₀.sub (hp₀.const_mul 11)) (hm₀.const_mul 7),
    intervalIntegral.integral_sub hj₀ (hp₀.const_mul 11), sub_zero] at hnear
  simp only [intervalIntegral.integral_const_mul] at hnear
  have hfarInt : IntegrableOn (fun t ↦ diagonalWeightedDifference t -
      11 * diagonalPlusBetaDensity t) (Ioi (1 / 2 : ℝ)) := hj₁.sub (hp₁.const_mul 11)
  have hfarDeriv : ∀ t ∈ Ioi (1 / 2 : ℝ), HasDerivAt diagonalFarBoundary
      (diagonalWeightedDifference t - 11 * diagonalPlusBetaDensity t) t := by
    intro t ht
    have htt : (1 / 2 : ℝ) < t := ht
    have hd := hasDerivAt_diagonalFarBoundary (by linarith : 0 < t)
    simpa only [diagonalWeightedDifference, diagonalDifference,
      ite_eq_right (not_le.mpr htt), diagonalFarDifference] using hd
  have hfarCont : ContinuousWithinAt diagonalFarBoundary (Ici (1 / 2 : ℝ)) (1 / 2) :=
    (hasDerivAt_diagonalFarBoundary
      (by norm_num : (0 : ℝ) < 1 / 2)).continuousAt.continuousWithinAt
  have hfar := integral_Ioi_of_hasDerivAt_of_tendsto
    hfarCont hfarDeriv hfarInt tendsto_diagonalFarBoundary_atTop
  rw [integral_sub hj₁ (hp₁.const_mul 11), integral_const_mul, zero_sub] at hfar
  have hjSplit := intervalIntegral.integral_interval_add_Ioi
    integrableOn_diagonalWeightedDifference hj₁
  have hpSplit := intervalIntegral.integral_interval_add_Ioi
    integrableOn_diagonalPlusBetaDensity hp₁
  rw [integral_diagonalPlusBetaDensity] at hpSplit
  rw [integral_diagonalMinusBetaDensity_half, diagonalNearBoundary_half_eq_far] at hnear
  linarith

/-- The actual paired coordinate generator at the fixed diagonal has the intrinsic constant. -/
theorem diamondPairedGenerator_diagonal_eq_intrinsic :
    diamondPairedGenerator (6 / 5) (1 / 2) (1 / 2) = squareIntrinsicConstant := by
  rw [diamondPairedGenerator_diagonal_eq_integral,
    integral_diagonalWeightedDifference_eq_positiveBeta]
  calc
    _ = 22 * realBetaIntegral (4 / 5) (12 / 5) -
        7 * realBetaIntegral (4 / 5) (4 / 5) := by ring
    _ = _ := diagonal_positiveBeta_normalization

/-- The actual homogeneous paired generator has its exact radial source at every positive point. -/
theorem diamondPairedGenerator_eq_intrinsic {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    diamondPairedGenerator (6 / 5) u v =
      (u + v) ^ (-12 / 5 : ℝ) * squareIntrinsicConstant := by
  rw [diamondPairedGenerator_eq_diagonal
    (by norm_num : (0 : ℝ) < 6 / 5) (by norm_num : (6 / 5 : ℝ) < 2) hu hv,
      diamondPairedGenerator_diagonal_eq_intrinsic]
  congr 2
  ring

end PartialBalayage.Maximal.Square
