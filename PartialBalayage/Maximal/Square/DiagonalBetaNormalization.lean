/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RealBetaIntegral
public import PartialBalayage.Maximal.Square.GeneratorConstantBound

/-!
# Exact positive-beta normalization of the diagonal source

Actual Gamma recurrence and reflection identify the two convergent positive
beta integrals arising from ordinary integration by parts with the genuine
intrinsic constant. No negative-parameter beta integral is introduced.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

theorem Gamma_four_fifths_mul_six_fifths :
    Real.Gamma (4 / 5) * Real.Gamma (6 / 5) =
      Real.pi / (5 * Real.sin (Real.pi / 5)) := by
  have hrec := Real.Gamma_add_one (by norm_num : (1 / 5 : ℝ) ≠ 0)
  norm_num only [show (1 / 5 : ℝ) + 1 = 6 / 5 by ring] at hrec
  have href := Real.Gamma_mul_Gamma_one_sub (1 / 5 : ℝ)
  norm_num only [show (1 : ℝ) - 1 / 5 = 4 / 5 by ring] at href
  rw [hrec]
  calc
    _ = (1 / 5 : ℝ) * (Real.Gamma (1 / 5) * Real.Gamma (4 / 5)) := by ring
    _ = _ := by
      rw [href, show Real.pi * (1 / 5) = Real.pi / 5 by ring]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem Gamma_eight_fifths_mul_twelve_fifths :
    Real.Gamma (8 / 5) * Real.Gamma (12 / 5) =
      42 * Real.pi / (125 * Real.sin (2 * Real.pi / 5)) := by
  have h₃ := Real.Gamma_add_one (by norm_num : (3 / 5 : ℝ) ≠ 0)
  have h₂ := Real.Gamma_add_one (by norm_num : (2 / 5 : ℝ) ≠ 0)
  have h₇ := Real.Gamma_add_one (by norm_num : (7 / 5 : ℝ) ≠ 0)
  norm_num only [show (3 / 5 : ℝ) + 1 = 8 / 5 by ring] at h₃
  norm_num only [show (2 / 5 : ℝ) + 1 = 7 / 5 by ring] at h₂
  norm_num only [show (7 / 5 : ℝ) + 1 = 12 / 5 by ring] at h₇
  have href := Real.Gamma_mul_Gamma_one_sub (2 / 5 : ℝ)
  norm_num only [show (1 : ℝ) - 2 / 5 = 3 / 5 by ring] at href
  rw [h₃, h₇, h₂]
  calc
    _ = (42 / 125 : ℝ) * (Real.Gamma (2 / 5) * Real.Gamma (3 / 5)) := by ring
    _ = _ := by
      rw [href, show Real.pi * (2 / 5) = 2 * Real.pi / 5 by ring]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem Gamma_sixteen_fifths :
    Real.Gamma (16 / 5) = (66 / 25 : ℝ) * Real.Gamma (6 / 5) := by
  have h₆ := Real.Gamma_add_one (by norm_num : (6 / 5 : ℝ) ≠ 0)
  have h₁₁ := Real.Gamma_add_one (by norm_num : (11 / 5 : ℝ) ≠ 0)
  norm_num only [show (6 / 5 : ℝ) + 1 = 11 / 5 by ring] at h₆
  norm_num only [show (11 / 5 : ℝ) + 1 = 16 / 5 by ring] at h₁₁
  rw [h₁₁, h₆]
  ring

theorem sin_pi_div_five_ne_zero : Real.sin (Real.pi / 5) ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'

/-- The genuine half-angle identity in a form matching actual Gamma reflection. -/
theorem tan_pi_div_ten_eq_one_sub_cos_div_sin :
    Real.tan (Real.pi / 10) =
      (1 - Real.cos (Real.pi / 5)) / Real.sin (Real.pi / 5) := by
  have hc : Real.cos (Real.pi / 10) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩).ne'
  have hangle : 2 * (Real.pi / 10) = Real.pi / 5 := by ring
  have hsin := Real.sin_two_mul (Real.pi / 10)
  have hcos := Real.cos_two_mul (Real.pi / 10)
  rw [hangle] at hsin hcos
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc, sin_pi_div_five_ne_zero]
  rw [hsin, hcos]
  have hs : Real.sin (Real.pi / 10) ^ 2 = 1 - Real.cos (Real.pi / 10) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 10)]
  calc
    _ = 2 * Real.cos (Real.pi / 10) * Real.sin (Real.pi / 10) ^ 2 := by ring
    _ = _ := by rw [hs]; ring

/-- Two actual convergent positive beta integrals have the exact intrinsic normalization. -/
theorem diagonal_positiveBeta_normalization :
    22 * realBetaIntegral (4 / 5) (12 / 5) -
      7 * realBetaIntegral (4 / 5) (4 / 5) = squareIntrinsicConstant := by
  have h₆ : Real.Gamma (6 / 5) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 6 / 5)).ne'
  have h₈ : Real.Gamma (8 / 5) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 8 / 5)).ne'
  have h₁₂ : Real.Gamma (12 / 5) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 12 / 5)).ne'
  have hd : (6 / 5 : ℝ) * squareBetaIntegral ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) squareBetaIntegral_pos)
  unfold squareIntrinsicConstant
  apply (eq_div_iff hd).mpr
  rw [squareBetaIntegral_eq_realBetaIntegral]
  rw [realBetaIntegral_eq_Gamma_mul_div (by norm_num : (0 : ℝ) < 4 / 5)
      (by norm_num : (0 : ℝ) < 12 / 5),
    realBetaIntegral_eq_Gamma_mul_div (by norm_num : (0 : ℝ) < 4 / 5)
      (by norm_num : (0 : ℝ) < 4 / 5),
    realBetaIntegral_eq_Gamma_mul_div (by norm_num : (0 : ℝ) < 6 / 5)
      (by norm_num : (0 : ℝ) < 6 / 5)]
  norm_num only [show (4 / 5 : ℝ) + 12 / 5 = 16 / 5 by ring,
    show (4 / 5 : ℝ) + 4 / 5 = 8 / 5 by ring,
    show (6 / 5 : ℝ) + 6 / 5 = 12 / 5 by ring]
  rw [Gamma_sixteen_fifths]
  have he :
      (22 * (Real.Gamma (4 / 5) * Real.Gamma (12 / 5) /
        ((66 / 25 : ℝ) * Real.Gamma (6 / 5))) -
          7 * (Real.Gamma (4 / 5) * Real.Gamma (4 / 5) / Real.Gamma (8 / 5))) *
        ((6 / 5 : ℝ) * (Real.Gamma (6 / 5) * Real.Gamma (6 / 5) /
          Real.Gamma (12 / 5))) =
      10 * (Real.Gamma (4 / 5) * Real.Gamma (6 / 5)) - (42 / 5 : ℝ) *
        (Real.Gamma (4 / 5) * Real.Gamma (6 / 5)) ^ 2 /
          (Real.Gamma (8 / 5) * Real.Gamma (12 / 5)) := by
    field_simp
    ring
  rw [he, Gamma_four_fifths_mul_six_fifths, Gamma_eight_fifths_mul_twelve_fifths,
    tan_pi_div_ten_eq_one_sub_cos_div_sin]
  have hsin : Real.sin (2 * Real.pi / 5) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
  have hdouble : Real.sin (2 * Real.pi / 5) =
      2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) := by
    convert Real.sin_two_mul (Real.pi / 5) using 1
    congr 1
    ring
  field_simp [sin_pi_div_five_ne_zero, hsin, Real.pi_ne_zero]
  rw [show Real.pi * 2 / 5 = 2 * Real.pi / 5 by ring, hdouble]
  ring

end PartialBalayage.Maximal.Square
