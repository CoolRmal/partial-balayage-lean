/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiagonalBetaPrimitives
public import PartialBalayage.Maximal.Square.RadialEndpointLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual diagonal integration-by-parts boundary functions

Genuine ordinary primitives cancel the singular origin and the infinite
endpoint. Their two smooth pieces agree at the actual crossing point.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PartialBalayage.Maximal.Square

def diagonalNearDifference (t : ℝ) : ℝ :=
  (1 + t) ^ (-6 / 5 : ℝ) + (1 - t) ^ (-6 / 5 : ℝ) - 2

def diagonalFarDifference (t : ℝ) : ℝ :=
  (1 + t) ^ (-6 / 5 : ℝ) + t ^ (-6 / 5 : ℝ) - 2

/-- The true origin-side boundary function from two ordinary integrations by parts. -/
def diagonalNearBoundary (t : ℝ) : ℝ :=
  (-5 / 6 : ℝ) * t ^ (-6 / 5 : ℝ) * diagonalNearDifference t +
    5 * diagonalPlusPrimitive t + diagonalMinusPrimitive t

/-- The true exterior-side boundary function. -/
def diagonalFarBoundary (t : ℝ) : ℝ :=
  (-5 / 6 : ℝ) * t ^ (-6 / 5 : ℝ) * diagonalFarDifference t +
    5 * diagonalPlusPrimitive t + (5 / 12 : ℝ) * t ^ (-12 / 5 : ℝ)

theorem hasDerivAt_diagonalNearBoundary {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    HasDerivAt diagonalNearBoundary
      (t ^ (-11 / 5 : ℝ) * diagonalNearDifference t -
        11 * diagonalPlusBetaDensity t + 7 * diagonalMinusBetaDensity t) t := by
  have hq : 0 < 1 - t := by linarith
  have htp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hd₁ := Real.hasDerivAt_rpow_const (p := (-6 / 5 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := (-6 / 5 : ℝ)) (Or.inl htp)
  have hd₃ := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := (-6 / 5 : ℝ)) (Or.inl hq.ne')
  have hd := ((((hd₁.const_mul (-5 / 6)).mul ((hd₂.add hd₃).sub_const 2)).add
    ((hasDerivAt_diagonalPlusPrimitive ht).const_mul 5)).add
      (hasDerivAt_diagonalMinusPrimitive ht ht₁))
  convert hd using 1
  · rfl
  · simp only [diagonalNearDifference, id_eq, Pi.add_apply,
      show (-6 / 5 : ℝ) - 1 = -11 / 5 by ring]
    ring

theorem hasDerivAt_diagonalFarBoundary {t : ℝ} (ht : 0 < t) :
    HasDerivAt diagonalFarBoundary
      (t ^ (-11 / 5 : ℝ) * diagonalFarDifference t -
        11 * diagonalPlusBetaDensity t) t := by
  have htp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hd₁ := Real.hasDerivAt_rpow_const (p := (-6 / 5 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := (-6 / 5 : ℝ)) (Or.inl htp)
  have hd₃ := Real.hasDerivAt_rpow_const (p := (-12 / 5 : ℝ)) (Or.inl ht.ne')
  have hd := ((((hd₁.const_mul (-5 / 6)).mul ((hd₂.add hd₁).sub_const 2)).add
    ((hasDerivAt_diagonalPlusPrimitive ht).const_mul 5)).add
      (hd₃.const_mul (5 / 12)))
  have hp : t ^ (-6 / 5 : ℝ) * t ^ (-11 / 5 : ℝ) = t ^ (-17 / 5 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  convert hd using 1
  · rfl
  · simp only [diagonalFarDifference, id_eq, Pi.add_apply,
      show (-6 / 5 : ℝ) - 1 = -11 / 5 by ring,
      show (-12 / 5 : ℝ) - 1 = -17 / 5 by ring]
    have he : t ^ (-11 / 5 : ℝ) * t ^ (-6 / 5 : ℝ) = t ^ (-17 / 5 : ℝ) :=
      (mul_comm _ _).trans hp
    rw [mul_add, mul_sub, mul_add, he]
    nlinarith only [hp]

theorem diagonalMinusPrimitive_half :
    diagonalMinusPrimitive (1 / 2) = (5 / 12 : ℝ) * (1 / 2 : ℝ) ^ (-12 / 5 : ℝ) := by
  have hp : (1 / 2 : ℝ) ^ (-12 / 5 : ℝ) =
      2 * (1 / 2 : ℝ) ^ (-7 / 5 : ℝ) := by
    calc
      _ = (1 / 2 : ℝ) ^ ((-7 / 5 : ℝ) - 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub (by norm_num), Real.rpow_one]; ring
  simp only [diagonalMinusPrimitive, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    show (1 : ℝ) - 2 * (1 / 2) = 0 by ring, mul_zero, zero_mul, sub_zero]
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2), hp]
  rw [show (-1 / 5 : ℝ) + -6 / 5 = -7 / 5 by ring]
  ring

theorem diagonalNearBoundary_half_eq_far :
    diagonalNearBoundary (1 / 2) = diagonalFarBoundary (1 / 2) := by
  simp only [diagonalNearBoundary, diagonalFarBoundary, diagonalNearDifference,
    diagonalFarDifference, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    diagonalMinusPrimitive_half]

/-- The true divergent primitive terms cancel at the origin. -/
theorem tendsto_diagonalNearBoundary_zero :
    Tendsto diagonalNearBoundary (𝓝[>] 0) (𝓝 0) := by
  have hdiff : Tendsto (fun t : ℝ ↦ t ^ (-6 / 5 : ℝ) * diagonalNearDifference t)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [diagonalNearDifference, mul_one, Real.one_rpow,
      show -(6 / 5 : ℝ) = -6 / 5 by ring] using
        tendsto_rpow_mul_shifted_secondDifference
          (by norm_num : (0 : ℝ) < 6 / 5) (by norm_num : (6 / 5 : ℝ) < 2)
            (by norm_num : (0 : ℝ) < 1)
  let f : ℝ → ℝ := fun t ↦ 5 * (1 + t) ^ (-11 / 5 : ℝ) +
    (5 / 6 : ℝ) * (1 - t) ^ (-6 / 5 : ℝ) -
      (35 / 6 : ℝ) * (1 - 2 * t) * (1 - t) ^ (-1 / 5 : ℝ)
  have hf : DifferentiableAt ℝ f 0 := by
    dsimp only [f]
    fun_prop (disch := norm_num)
  have hf₀ : f 0 = 0 := by norm_num [f]
  have hrem := tendsto_rpow_mul_of_hasDerivAt_zero hf.hasDerivAt hf₀
    (by norm_num : (-1 : ℝ) < -1 / 5)
  have h := (hdiff.const_mul (-5 / 6 : ℝ)).add hrem
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards with t
  dsimp only [diagonalNearBoundary, diagonalPlusPrimitive, diagonalMinusPrimitive, f]
  ring

/-- The genuine exterior boundary terms vanish at infinity. -/
theorem tendsto_diagonalFarBoundary_atTop :
    Tendsto diagonalFarBoundary atTop (𝓝 0) := by
  have h₁ : Tendsto (fun t : ℝ ↦ t ^ (-6 / 5 : ℝ)) atTop (𝓝 0) := by
    simpa only [show -(6 / 5 : ℝ) = -6 / 5 by ring] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 6 / 5)
  have h₂ : Tendsto (fun t : ℝ ↦ (1 + t) ^ (-6 / 5 : ℝ)) atTop (𝓝 0) :=
    h₁.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have h₃ : Tendsto (fun t : ℝ ↦ t ^ (-1 / 5 : ℝ)) atTop (𝓝 0) := by
    simpa only [show -(1 / 5 : ℝ) = -1 / 5 by ring] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)
  have h₄ : Tendsto (fun t : ℝ ↦ (1 + t) ^ (-11 / 5 : ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ ↦ (1 + t) ^ (-(11 / 5 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 5)).comp
        (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa only [show -(11 / 5 : ℝ) = -11 / 5 by ring] using hh
  have h₅ : Tendsto (fun t : ℝ ↦ t ^ (-12 / 5 : ℝ)) atTop (𝓝 0) := by
    simpa only [show -(12 / 5 : ℝ) = -12 / 5 by ring] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 12 / 5)
  have h := (((h₁.const_mul (-5 / 6 : ℝ)).mul ((h₂.add h₁).sub_const 2)).add
    ((h₃.mul h₄).const_mul 5)).add (h₅.const_mul (5 / 12 : ℝ))
  simp only [mul_zero, zero_add, zero_mul] at h
  apply h.congr'
  filter_upwards with t
  dsimp only [diagonalFarBoundary, diagonalFarDifference, diagonalPlusPrimitive]

end PartialBalayage.Maximal.Square
