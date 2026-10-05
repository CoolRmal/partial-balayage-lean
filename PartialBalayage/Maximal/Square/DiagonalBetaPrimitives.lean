/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondCoordinateIntegral
public import PartialBalayage.Maximal.Square.BetaPrimeIntegral

/-!
# Actual positive-beta primitives for the diagonal integral

Ordinary derivatives turn the singular plus and minus kernels into
genuinely convergent positive beta densities and explicit endpoint terms.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual positive half-interval beta density. -/
def diagonalMinusBetaDensity (t : ℝ) : ℝ :=
  t ^ (-1 / 5 : ℝ) * (1 - t) ^ (-1 / 5 : ℝ)

/-- The actual positive beta-prime density. -/
def diagonalPlusBetaDensity (t : ℝ) : ℝ :=
  t ^ (-1 / 5 : ℝ) * (1 + t) ^ (-16 / 5 : ℝ)

/-- The genuine minus-kernel endpoint primitive. -/
def diagonalMinusPrimitive (t : ℝ) : ℝ :=
  (5 / 6 : ℝ) * t ^ (-1 / 5 : ℝ) * (1 - t) ^ (-6 / 5 : ℝ) -
    (35 / 6 : ℝ) * (1 - 2 * t) * t ^ (-1 / 5 : ℝ) * (1 - t) ^ (-1 / 5 : ℝ)

/-- The genuine plus-kernel endpoint primitive. -/
def diagonalPlusPrimitive (t : ℝ) : ℝ :=
  t ^ (-1 / 5 : ℝ) * (1 + t) ^ (-11 / 5 : ℝ)

theorem hasDerivAt_diagonalPlusPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt diagonalPlusPrimitive
      ((-1 / 5 : ℝ) * t ^ (-6 / 5 : ℝ) * (1 + t) ^ (-11 / 5 : ℝ) -
        (11 / 5 : ℝ) * diagonalPlusBetaDensity t) t := by
  have htp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hd₁ := Real.hasDerivAt_rpow_const
    (p := (-1 / 5 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := (-11 / 5 : ℝ)) (Or.inl htp)
  convert hd₁.mul hd₂ using 1
  · rfl
  · simp only [diagonalPlusBetaDensity, id_eq,
      show (-1 / 5 : ℝ) - 1 = -6 / 5 by ring,
      show (-11 / 5 : ℝ) - 1 = -16 / 5 by ring]
    ring

/-- The actual minus primitive leaves exactly the integrable positive beta density. -/
theorem hasDerivAt_diagonalMinusPrimitive {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    HasDerivAt diagonalMinusPrimitive
      (t ^ (-6 / 5 : ℝ) * (1 - t) ^ (-11 / 5 : ℝ) +
        7 * diagonalMinusBetaDensity t) t := by
  have hq : 0 < 1 - t := by linarith
  have hd₁ := Real.hasDerivAt_rpow_const (p := (-1 / 5 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := (-6 / 5 : ℝ)) (Or.inl hq.ne')
  have hd₃ := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := (-1 / 5 : ℝ)) (Or.inl hq.ne')
  have hd₄ := ((hasDerivAt_id t).const_mul 2).const_sub 1
  have hd := (((hd₁.const_mul (5 / 6)).mul hd₂).sub
    ((((hd₄.const_mul (35 / 6)).mul hd₁).mul hd₃)))
  have hp : t ^ (-6 / 5 : ℝ) = t ^ (-1 / 5 : ℝ) / t := by
    calc
      _ = t ^ ((-1 / 5 : ℝ) - 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub ht, Real.rpow_one]
  have hq₁ : (1 - t) ^ (-6 / 5 : ℝ) = (1 - t) ^ (-1 / 5 : ℝ) / (1 - t) := by
    calc
      _ = (1 - t) ^ ((-1 / 5 : ℝ) - 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hq, Real.rpow_one]
  have hq₂ : (1 - t) ^ (-11 / 5 : ℝ) = (1 - t) ^ (-1 / 5 : ℝ) / (1 - t) ^ 2 := by
    calc
      _ = (1 - t) ^ ((-1 / 5 : ℝ) - 2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hq, Real.rpow_two]
  convert hd using 1
  · rfl
  · simp only [diagonalMinusBetaDensity, id_eq, Pi.mul_apply,
      show (-1 / 5 : ℝ) - 1 = -6 / 5 by ring,
      show (-6 / 5 : ℝ) - 1 = -11 / 5 by ring]
    rw [hp, hq₁, hq₂]
    field_simp
    ring

end PartialBalayage.Maximal.Square
