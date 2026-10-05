/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorRectangleLower
public import PartialBalayage.Maximal.Square.Data.GeneratorLeafCheck0
public import PartialBalayage.Maximal.Square.RadialModelLower

/-!
# Genuine pointwise positivity on the first generator rectangle

The concrete data's exact positive rational bound is connected to the actual
signed spline correction and the actual radial incoming-tail expression. The
conclusion applies throughout the rectangle's strict support interior; no
external arithmetic or generator-positivity premise enters the theorem.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The explicit normalized strict-interior source density in the unit-grid coordinates. -/
def generatorInteriorDensity (u v : ℝ) : ℝ :=
  radialCoefficient *
    (squareIntrinsicConstant * ((u + v) / 16) ^ (-12 / 5 : ℝ) +
      radialIncomingTail (6 / 5) supportRadius ((u + v) / 16) ((u - v) / 16)) +
    splineGeneratorFactor * splineGeneratorCorrectionPower u v

/-- The actual source expression is positive on the entire first rectangle's interior part. -/
theorem generatorInteriorDensity_pos_first_rectangle {t s : ℝ}
    (ht₀ : 1 / 2 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hr : 27 + t + s < 28) : 0 < generatorInteriorDensity (27 + t) s := by
  let U := generatorCubicData_27_1_1
  let V := generatorCubicData_0_1_0
  let H := generatorPowerFamily_27_1_1
  let J := generatorPowerFamily_0_1_0
  let D := generatorRadialPlane0
  let a : ℚ := 11248245541992991 / 6250000000000000
  let S : ℚ := 125337337 / 50000000
  let ρ := generatorRadiusInterval.lower
  let rI := radialRectangleIntervals D S ρ (7 / 4) a
    (111 / 4) (1 / 4) (111 / 4) (1 / 4)
  let rc := radialRectangleCoefficients D S ρ (7 / 4) a
    (111 / 4) (1 / 4) (111 / 4) (1 / 4)
  have hU : U.IsValid := generatorCubicData_27_1_1_valid
  have hV : V.IsValid := generatorCubicData_0_1_0_valid
  have hH : ∀ k, (H k).IsValid := generatorPowerFamily_27_1_1_valid
  have hJ : ∀ k, (J k).IsValid := generatorPowerFamily_0_1_0_valid
  have hD : D.IsValid := generatorRadialPlane0_valid
  have hcH (k : Fin 53) :
      (H k).center = (U.cell.val : ℚ) + U.midpoint - (generatorKnot k : ℚ) := by
    rw [generatorPowerFamily_27_1_1_center]
    norm_num [U, generatorCubicData_27_1_1, GeneratorCubicIntervalData.midpoint, generatorKnot]
  have hcJ (k : Fin 53) :
      (J k).center = (V.cell.val : ℚ) + V.midpoint - (generatorKnot k : ℚ) := by
    rw [generatorPowerFamily_0_1_0_center]
    norm_num [V, generatorCubicData_0_1_0, GeneratorCubicIntervalData.midpoint, generatorKnot]
  have hrH (k : Fin 53) : (H k).radius = U.width / 2 := by
    rw [generatorPowerFamily_27_1_1_radius]
    norm_num [U, generatorCubicData_27_1_1]
  have hrJ (k : Fin 53) : (J k).radius = V.width / 2 := by
    rw [generatorPowerFamily_0_1_0_radius]
    norm_num [V, generatorCubicData_0_1_0]
  have hRI (p : RectangleIndex) : (rI p).Contains (rc p) :=
    radialRectangleIntervals_contains hD S ρ (7 / 4) a
      (111 / 4) (1 / 4) (111 / 4) (1 / 4) p
  have hu₀ : (U.lower : ℝ) ≤ t := by simpa [U, generatorCubicData_27_1_1] using ht₀
  have hu₁ : t ≤ ((U.lower + U.width : ℚ) : ℝ) := by
    convert ht₁ using 1
    norm_num [U, generatorCubicData_27_1_1]
  have hv₀ : (V.lower : ℝ) ≤ s := by
    simpa [V, generatorCubicData_0_1_0] using hs₀.le
  have hv₁ : s ≤ ((V.lower + V.width : ℚ) : ℝ) := by
    simpa [V, generatorCubicData_0_1_0] using hs₁
  have hδU : U.width / 2 = (1 / 4 : ℚ) := by norm_num [U, generatorCubicData_27_1_1]
  have hδV : V.width / 2 = (1 / 4 : ℚ) := by norm_num [V, generatorCubicData_0_1_0]
  have hLow := generatorCombinedIntervals_lower hU hV hH hJ hcH hcJ hrH hrJ
    splineGeneratorFactorInterval_contains splineGeneratorFactorInterval_lower_nonneg
    hRI hδU hδV (by linarith : 0 ≤ t) ht₁ hs₀.le (by linarith : s ≤ 1)
    hu₀ hu₁ hv₀ hv₁
  have hUM : (U.midpoint : ℝ) = 3 / 4 := by
    norm_num [U, generatorCubicData_27_1_1, GeneratorCubicIntervalData.midpoint]
  have hVM : (V.midpoint : ℝ) = 1 / 4 := by
    norm_num [V, generatorCubicData_0_1_0, GeneratorCubicIntervalData.midpoint]
  have hUC : (U.cell.val : ℝ) = 27 := by norm_num [U, generatorCubicData_27_1_1]
  have hVC : (V.cell.val : ℝ) = 0 := by norm_num [V, generatorCubicData_0_1_0]
  rw [hUM, hVM, hUC, hVC, zero_add] at hLow
  have hCI : generatorCombinedIntervals U V H J splineGeneratorFactorInterval rI =
      firstGeneratorLeafIntervals := by funext p; rfl
  rw [hCI] at hLow
  have hLow' : (firstGeneratorLeafLowerBound : ℝ) ≤
      splineGeneratorFactor * splineGeneratorCorrectionPower (27 + t) s +
        rectanglePolynomial rc (t - 3 / 4) (s - 1 / 4) := by
    simpa only [firstGeneratorLeafLowerBound, firstGeneratorLeafError, U, V, H, J] using hLow
  have hR₀ : D.radius = (111 / 4 + 1 / 4 : ℚ) / 16 := by norm_num [D, generatorRadialPlane0]
  have hDd₀ : D.difference = (111 / 4 - 1 / 4 : ℚ) / 16 := by
    norm_num [D, generatorRadialPlane0]
  have hpoly := radialRectanglePolynomial_eq D S ρ (7 / 4) a
    (111 / 4) (1 / 4) (111 / 4) (1 / 4) hR₀ hDd₀ (27 + t) s
  have hx : 27 + t - (111 / 4 : ℝ) = t - 3 / 4 := by ring
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hpoly
  rw [hx] at hpoly
  have hS₀ : (0 : ℝ) ≤ (S : ℝ) := by norm_num [S]
  have hρ₀ : (0 : ℝ) ≤ (ρ : ℝ) := by norm_num [ρ, generatorRadiusInterval]
  have hSu : (S : ℝ) ≤ squareIntrinsicConstant := by
    simpa only [S, Rat.cast_div, Rat.cast_ofNat] using squareIntrinsicConstant_ge
  have hρu : (ρ : ℝ) ≤ (7 / 4 : ℝ) ^ (-12 / 5 : ℝ) := by
    simpa only [ρ, supportRadius] using generatorRadiusInterval_contains.1
  have hrad : 0 < ((27 : ℝ) + t + s) / 16 := by linarith
  have hradR : ((27 : ℝ) + t + s) / 16 < 7 / 4 := by linarith
  have hdiff : |((27 : ℝ) + t - s) / 16| < 7 / 4 := by
    apply abs_lt.mpr
    constructor <;> linarith
  have htangent := radialGeneratorLowerModel_tangent_le_analytic
    (S := (S : ℝ)) (ρ := (ρ : ℝ)) (R := (7 / 4 : ℝ))
    (r₀ := (D.radius : ℝ)) (d₀ := (D.difference : ℝ))
    (r := ((27 : ℝ) + t + s) / 16) (d := ((27 : ℝ) + t - s) / 16) D.terms hS₀ hρ₀
    (by norm_num : (0 : ℝ) < 7 / 4) (by exact_mod_cast hD.1) hrad hradR hdiff hSu hρu
  have ha : (0 : ℝ) ≤ (a : ℝ) := by norm_num [a]
  have hplane : rectanglePolynomial rc (t - 3 / 4) (s - 1 / 4) ≤
      radialCoefficient *
        (squareIntrinsicConstant * ((27 + t + s) / 16) ^ (-12 / 5 : ℝ) +
          radialIncomingTail (6 / 5) supportRadius ((27 + t + s) / 16)
            ((27 + t - s) / 16)) := by
    rw [show rectanglePolynomial rc (t - 3 / 4) (s - 1 / 4) = _ from hpoly]
    simpa only [a, S, radialCoefficient, supportRadius, Rat.cast_div, Rat.cast_ofNat] using
      mul_le_mul_of_nonneg_left htangent ha
  have hLB : (0 : ℝ) < (firstGeneratorLeafLowerBound : ℝ) := by
    exact_mod_cast firstGeneratorLeafLowerBound_pos
  have h := hLB.trans_le (hLow'.trans (add_le_add le_rfl hplane))
  simpa only [generatorInteriorDensity, add_comm] using h

end PartialBalayage.Maximal.Square
