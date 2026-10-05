/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.AbsPowerTaylor
public import PartialBalayage.Maximal.Square.RationalInterval

/-!
# Exact enclosures of genuine spline-generator Taylor coefficients

Four ordinary rational fifth-power checks enclose the actual cubic coefficients.
A fifth such check supplies the rigorous far-knot remainder. Intervals touching a
knot instead use the genuine linear approximation and its proved boundary error.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The exact sign used by the rational coefficient calculation. -/
def rationalCenterSign (a : ℚ) : ℚ := if 0 < a then 1 else -1

theorem rationalCenterSign_cast (a : ℚ) :
    (rationalCenterSign a : ℝ) = powerCenterSign (a : ℝ) := by
  unfold rationalCenterSign powerCenterSign
  split_ifs with h h' h'
  · norm_num
  · exact False.elim (h' (by exact_mod_cast h))
  · exact False.elim (h (by exact_mod_cast h'))
  · norm_num

/-- Actual cubic coefficients in powers of the displacement from the center. -/
def absPowerTaylorCoefficients (a : ℝ) : Fin 4 → ℝ :=
  ![|a| ^ (9 / 5 : ℝ), (9 / 5 : ℝ) * powerCenterSign a * |a| ^ (4 / 5 : ℝ),
    (18 / 25 : ℝ) * |a| ^ (-1 / 5 : ℝ),
    (-6 / 125 : ℝ) * powerCenterSign a * |a| ^ (-6 / 5 : ℝ)]

/-- Rational interval coefficients assembled from the four genuine powers. -/
def absPowerTaylorIntervals (a : ℚ) (P : Fin 4 → RationalInterval) :
    Fin 4 → RationalInterval :=
  ![P 0, (P 1).scale ((9 / 5) * rationalCenterSign a), (P 2).scale (18 / 25),
    (P 3).scale ((-6 / 125) * rationalCenterSign a)]

/-- The four exact integer numerators of the fractional exponents. -/
def absPowerTaylorExponents : Fin 4 → ℤ := ![9, 4, -1, -6]

theorem absPowerTaylorCoefficients_eval (a x : ℝ) :
    (∑ i : Fin 4, absPowerTaylorCoefficients a i * (x - a) ^ i.val) =
      absPowerTaylorThree a x := by
  simp only [Fin.sum_univ_succ, absPowerTaylorCoefficients, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num [absPowerTaylorThree]
  ring

/-- Ordinary fifth-power checks enclose every actual cubic Taylor coefficient. -/
theorem absPowerTaylorIntervals_contains (a : ℚ) (P : Fin 4 → RationalInterval)
    (hP : ∀ i, IsPowerEnclosure |a| (absPowerTaylorExponents i) (P i).lower (P i).upper) :
    ∀ i, (absPowerTaylorIntervals a P i).Contains
      (absPowerTaylorCoefficients (a : ℝ) i) := by
  have hp (i : Fin 4) := (hP i).rpow_bounds (abs_nonneg a)
  have h₀ : (P 0).Contains (|(a : ℝ)| ^ (9 / 5 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 0
  have h₁ : (P 1).Contains (|(a : ℝ)| ^ (4 / 5 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 1
  have h₂ : (P 2).Contains (|(a : ℝ)| ^ (-1 / 5 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 2
  have h₃ : (P 3).Contains (|(a : ℝ)| ^ (-6 / 5 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 3
  intro i
  fin_cases i
  · simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients] using h₀
  · have hb := h₁.scale ((9 / 5) * rationalCenterSign a)
    simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients,
      rationalCenterSign_cast] using hb
  · have hb := h₂.scale (18 / 25)
    simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients] using hb
  · have hb := h₃.scale ((-6 / 125) * rationalCenterSign a)
    simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients,
      rationalCenterSign_cast] using hb

/-- The far-knot error is bounded by a kernel-checked rational fifth-power enclosure. -/
theorem absPowerTaylorThree_error_le_rational {a δ : ℚ} {x : ℝ}
    (hδ : 0 ≤ δ) (haδ : δ < |a|) (hx : |x - (a : ℝ)| ≤ (δ : ℝ))
    (P : RationalInterval) (hP : IsPowerEnclosure (|a| - δ) (-11) P.lower P.upper) :
    |(|x| ^ (9 / 5 : ℝ) - absPowerTaylorThree (a : ℝ) x)| ≤
      ((9 / 625 * δ ^ (4 : ℕ) * P.upper : ℚ) : ℝ) := by
  have hδ' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have haδ' : (δ : ℝ) < |(a : ℝ)| := by exact_mod_cast haδ
  have hp := hP.rpow_bounds (by linarith : 0 ≤ |a| - δ)
  have hb := abs_absRpow_nine_fifths_sub_taylorThree_le hδ' haδ' hx
  apply hb.trans
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Rat.cast_sub, Rat.cast_abs, Int.cast_neg, Int.cast_ofNat] using hp.2

/-- The boundary-knot error uses its true linear remainder, including the knot itself. -/
theorem absPowerTaylorOne_error_le_rational {a : ℚ} {x : ℝ} (ha : a ≠ 0)
    (hx : |x - (a : ℝ)| ≤ |(a : ℝ)|) (P : RationalInterval)
    (hP : IsPowerEnclosure |a| 9 P.lower P.upper) :
    |(|x| ^ (9 / 5 : ℝ) - absPowerTaylorOne (a : ℝ) x)| ≤
      ((4 / 5 * P.upper : ℚ) : ℝ) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb := abs_absRpow_nine_fifths_sub_taylorOne_le ha' hx
  have hp := hP.rpow_bounds (abs_nonneg a)
  apply hb.trans
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [Rat.cast_abs, Int.cast_ofNat] using hp.2

end PartialBalayage.Maximal.Square
