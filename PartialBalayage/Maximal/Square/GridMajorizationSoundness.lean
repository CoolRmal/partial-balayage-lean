/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.SquareGridGeometry

/-!
# Assembly of actual triangle inequalities on closed grid cells

The outer edge and the unit-diamond edge are covered by the lower closed triangle.
The upper triangle is only needed strictly inside the corresponding index bound.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Actual nonnegativity throughout a retained cell follows from its checked triangles. -/
theorem kernel_nonneg_on_cell_of_triangle_bounds (k l : ℕ) (hkl : k + l ≤ 27)
    (hLower : ∀ p : ℝ × ℝ, lowerCellTriangle.Contains p →
      0 ≤ kernel (((k : ℝ) + p.1) / 16) (((l : ℝ) + p.2) / 16))
    (hUpper : k + l ≤ 26 → ∀ p : ℝ × ℝ, upperCellTriangle.Contains p →
      0 ≤ kernel (((k : ℝ) + p.1) / 16) (((l : ℝ) + p.2) / 16))
    {t s : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : (k : ℝ) + l + t + s ≤ 28) :
    0 ≤ kernel (((k : ℝ) + t) / 16) (((l : ℝ) + s) / 16) := by
  by_cases h : t + s ≤ 1
  · exact hLower (t, s) (lowerCellTriangle_contains ht₀ hs₀ h)
  have hkl' : k + l ≤ 26 := by
    by_contra hc
    have heq : k + l = 27 := by omega
    have heq' : (k : ℝ) + l = 27 := by exact_mod_cast heq
    linarith
  exact hUpper hkl' (t, s) (upperCellTriangle_contains ht₁ hs₁ (by linarith))

/-- Actual unit-diamond majorization follows from the checked closed cell triangles. -/
theorem one_le_kernel_on_cell_of_triangle_bounds (k l : ℕ) (hkl : k + l ≤ 15)
    (hLower : ∀ p : ℝ × ℝ, lowerCellTriangle.Contains p →
      1 ≤ kernel (((k : ℝ) + p.1) / 16) (((l : ℝ) + p.2) / 16))
    (hUpper : k + l ≤ 14 → ∀ p : ℝ × ℝ, upperCellTriangle.Contains p →
      1 ≤ kernel (((k : ℝ) + p.1) / 16) (((l : ℝ) + p.2) / 16))
    {t s : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : (k : ℝ) + l + t + s ≤ 16) :
    1 ≤ kernel (((k : ℝ) + t) / 16) (((l : ℝ) + s) / 16) := by
  by_cases h : t + s ≤ 1
  · exact hLower (t, s) (lowerCellTriangle_contains ht₀ hs₀ h)
  have hkl' : k + l ≤ 14 := by
    by_contra hc
    have heq : k + l = 15 := by omega
    have heq' : (k : ℝ) + l = 15 := by exact_mod_cast heq
    linarith
  exact hUpper hkl' (t, s) (upperCellTriangle_contains ht₁ hs₁ (by linarith))

/-- Every point of the closed unit quarter diamond belongs to an actual retained cell. -/
theorem exists_closed_unit_diamond_grid {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : u + v ≤ 1) :
    ∃ k l : ℕ, k + l ≤ 15 ∧ ∃ t s : ℝ,
      0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ s ∧ s ≤ 1 ∧
        u = ((k : ℝ) + t) / 16 ∧ v = ((l : ℝ) + s) / 16 := by
  let k := Nat.floor (16 * u)
  let l := Nat.floor (16 * v)
  have hk : (k : ℝ) ≤ 16 * u := Nat.floor_le (by positivity)
  have hl : (l : ℝ) ≤ 16 * v := Nat.floor_le (by positivity)
  have hk' : 16 * u < (k : ℝ) + 1 := Nat.lt_floor_add_one (16 * u)
  have hl' : 16 * v < (l : ℝ) + 1 := Nat.lt_floor_add_one (16 * v)
  by_cases hkl : k + l ≤ 15
  · refine ⟨k, l, hkl, 16 * u - k, 16 * v - l, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals linarith
  have hkl' : k + l = 16 := by
    have hsum : ((k + l : ℕ) : ℝ) ≤ 16 := by push_cast; linarith
    have hsum' : k + l ≤ 16 := by exact_mod_cast hsum
    omega
  have hku : (k : ℝ) = 16 * u := by
    have hsum : (k : ℝ) + (l : ℝ) = 16 := by exact_mod_cast hkl'
    linarith
  have hlv : (l : ℝ) = 16 * v := by
    have hsum : (k : ℝ) + (l : ℝ) = 16 := by exact_mod_cast hkl'
    linarith
  by_cases hk₀ : k = 0
  · have hl₁₆ : l = 16 := by omega
    refine ⟨0, 15, by omega, 0, 1, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_, ?_⟩
    · simp only [hk₀, Nat.cast_zero] at hku
      norm_num
      linarith
    · simp only [hl₁₆, Nat.cast_ofNat] at hlv
      norm_num
      linarith
  · have hk₁ : 1 ≤ k := by omega
    refine ⟨k - 1, l, by omega, 1, 0, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_, ?_⟩
    · rw [Nat.cast_sub hk₁]
      norm_num only [Nat.cast_one]
      linarith
    · norm_num only [add_zero]
      linarith

end PartialBalayage.Maximal.Square
