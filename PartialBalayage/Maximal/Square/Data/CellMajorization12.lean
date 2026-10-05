/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves12
public import PartialBalayage.Maximal.Square.GridMajorizationSoundness

/-!
# Genuine midpoint coverage and actual closed-cell inequalities

The actual midpoint coverage theorem assembles all refined triangle inequalities.
Both the support boundary and the unit-diamond boundary are included.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

/-- The checked actual lower triangle of cell (11, 6), with every refinement covered. -/
theorem majorization_lower_11_6 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle507 := by decide +kernel
  have h := majorizationLeaf507_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (11, 6), with every refinement covered. -/
theorem majorization_upper_11_6 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle508 := by decide +kernel
  have h := majorizationLeaf508_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_11_6_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((11 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 11 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_11_6 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_11_6 hp)

/-- The checked actual lower triangle of cell (11, 7), with every refinement covered. -/
theorem majorization_lower_11_7 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle509 := by decide +kernel
  have h := majorizationLeaf509_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (11, 7), with every refinement covered. -/
theorem majorization_upper_11_7 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle510 := by decide +kernel
  have h := majorizationLeaf510_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_11_7_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((11 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + t) / 16)
      ((((7 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 11 7 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_11_7 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_11_7 hp)

/-- The checked actual lower triangle of cell (11, 8), with every refinement covered. -/
theorem majorization_lower_11_8 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle511 := by decide +kernel
  have h := majorizationLeaf511_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (11, 8), with every refinement covered. -/
theorem majorization_upper_11_8 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle512 := by decide +kernel
  have h := majorizationLeaf512_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_11_8_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((11 : ℕ) : ℝ) + ((8 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + t) / 16)
      ((((8 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 11 8 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_11_8 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_11_8 hp)

/-- The checked actual lower triangle of cell (11, 9), with every refinement covered. -/
theorem majorization_lower_11_9 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((9 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle513 := by decide +kernel
  have h := majorizationLeaf513_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (11, 9), with every refinement covered. -/
theorem majorization_upper_11_9 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((9 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle514 := by decide +kernel
  have h := majorizationLeaf514_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_11_9_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((11 : ℕ) : ℝ) + ((9 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + t) / 16)
      ((((9 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 11 9 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_11_9 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_11_9 hp)

/-- The checked actual lower triangle of cell (11, 10), with every refinement covered. -/
theorem majorization_lower_11_10 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((10 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle515 := by decide +kernel
  have h := majorizationLeaf515_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (11, 10), with every refinement covered. -/
theorem majorization_upper_11_10 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((10 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle516 := by decide +kernel
  have h := majorizationLeaf516_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_11_10_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((11 : ℕ) : ℝ) + ((10 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + t) / 16)
      ((((10 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 11 10 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_11_10 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_11_10 hp)

/-- The checked actual lower triangle of cell (11, 11), with every refinement covered. -/
theorem majorization_lower_11_11 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((11 : ℕ) : ℝ) + p.2) / 16) := by
  rcases RationalTriangle.contains_child_of_contains
    (lowerCellTriangle) hp with
    hp0 | hp1 | hp2 | hp3
  · rcases RationalTriangle.contains_child_of_contains
      ((lowerCellTriangle).child₀) hp0 with
      hp00 | hp01 | hp02 | hp03
    · have heq : ((lowerCellTriangle).child₀).child₀ =
          majorizationTriangle517 := by decide +kernel
      have h := majorizationLeaf517_kernel (heq ▸ hp00)
      simpa using h
    · have heq : ((lowerCellTriangle).child₀).child₁ =
          majorizationTriangle518 := by decide +kernel
      have h := majorizationLeaf518_kernel (heq ▸ hp01)
      simpa using h
    · have heq : ((lowerCellTriangle).child₀).child₂ =
          majorizationTriangle519 := by decide +kernel
      have h := majorizationLeaf519_kernel (heq ▸ hp02)
      simpa using h
    · rcases RationalTriangle.contains_child_of_contains
        (((lowerCellTriangle).child₀).child₃) hp03 with
        hp030 | hp031 | hp032 | hp033
      · have heq : (((lowerCellTriangle).child₀).child₃).child₀ =
            majorizationTriangle520 := by decide +kernel
        have h := majorizationLeaf520_kernel (heq ▸ hp030)
        simpa using h
      · have heq : (((lowerCellTriangle).child₀).child₃).child₁ =
            majorizationTriangle521 := by decide +kernel
        have h := majorizationLeaf521_kernel (heq ▸ hp031)
        simpa using h
      · have heq : (((lowerCellTriangle).child₀).child₃).child₂ =
            majorizationTriangle522 := by decide +kernel
        have h := majorizationLeaf522_kernel (heq ▸ hp032)
        simpa using h
      · have heq : (((lowerCellTriangle).child₀).child₃).child₃ =
            majorizationTriangle523 := by decide +kernel
        have h := majorizationLeaf523_kernel (heq ▸ hp033)
        simpa using h
  · have heq : (lowerCellTriangle).child₁ =
        majorizationTriangle524 := by decide +kernel
    have h := majorizationLeaf524_kernel (heq ▸ hp1)
    simpa using h
  · have heq : (lowerCellTriangle).child₂ =
        majorizationTriangle525 := by decide +kernel
    have h := majorizationLeaf525_kernel (heq ▸ hp2)
    simpa using h
  · rcases RationalTriangle.contains_child_of_contains
      ((lowerCellTriangle).child₃) hp3 with
      hp30 | hp31 | hp32 | hp33
    · have heq : ((lowerCellTriangle).child₃).child₀ =
          majorizationTriangle526 := by decide +kernel
      have h := majorizationLeaf526_kernel (heq ▸ hp30)
      simpa using h
    · have heq : ((lowerCellTriangle).child₃).child₁ =
          majorizationTriangle527 := by decide +kernel
      have h := majorizationLeaf527_kernel (heq ▸ hp31)
      simpa using h
    · have heq : ((lowerCellTriangle).child₃).child₂ =
          majorizationTriangle528 := by decide +kernel
      have h := majorizationLeaf528_kernel (heq ▸ hp32)
      simpa using h
    · have heq : ((lowerCellTriangle).child₃).child₃ =
          majorizationTriangle529 := by decide +kernel
      have h := majorizationLeaf529_kernel (heq ▸ hp33)
      simpa using h

/-- The checked actual upper triangle of cell (11, 11), with every refinement covered. -/
theorem majorization_upper_11_11 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + p.1) / 16)
      ((((11 : ℕ) : ℝ) + p.2) / 16) := by
  rcases RationalTriangle.contains_child_of_contains
    (upperCellTriangle) hp with
    hp0 | hp1 | hp2 | hp3
  · have heq : (upperCellTriangle).child₀ =
        majorizationTriangle530 := by decide +kernel
    have h := majorizationLeaf530_kernel (heq ▸ hp0)
    simpa using h
  · have heq : (upperCellTriangle).child₁ =
        majorizationTriangle531 := by decide +kernel
    have h := majorizationLeaf531_kernel (heq ▸ hp1)
    simpa using h
  · have heq : (upperCellTriangle).child₂ =
        majorizationTriangle532 := by decide +kernel
    have h := majorizationLeaf532_kernel (heq ▸ hp2)
    simpa using h
  · have heq : (upperCellTriangle).child₃ =
        majorizationTriangle533 := by decide +kernel
    have h := majorizationLeaf533_kernel (heq ▸ hp3)
    simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_11_11_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((11 : ℕ) : ℝ) + ((11 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((11 : ℕ) : ℝ) + t) / 16)
      ((((11 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 11 11 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_11_11 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_11_11 hp)

end PartialBalayage.Maximal.Square
