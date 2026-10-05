/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves18
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

/-- The checked actual lower triangle of cell (14, 3), with every refinement covered. -/
theorem majorization_lower_14_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle609 := by decide +kernel
  have h := majorizationLeaf609_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (14, 3), with every refinement covered. -/
theorem majorization_upper_14_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle610 := by decide +kernel
  have h := majorizationLeaf610_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_14_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((14 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 14 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_14_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_14_3 hp)

/-- The checked actual lower triangle of cell (14, 4), with every refinement covered. -/
theorem majorization_lower_14_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle611 := by decide +kernel
  have h := majorizationLeaf611_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (14, 4), with every refinement covered. -/
theorem majorization_upper_14_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle612 := by decide +kernel
  have h := majorizationLeaf612_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_14_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((14 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 14 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_14_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_14_4 hp)

/-- The checked actual lower triangle of cell (14, 5), with every refinement covered. -/
theorem majorization_lower_14_5 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle613 := by decide +kernel
  have h := majorizationLeaf613_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (14, 5), with every refinement covered. -/
theorem majorization_upper_14_5 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle614 := by decide +kernel
  have h := majorizationLeaf614_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_14_5_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((14 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 14 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_14_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_14_5 hp)

/-- The checked actual lower triangle of cell (14, 6), with every refinement covered. -/
theorem majorization_lower_14_6 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle615 := by decide +kernel
  have h := majorizationLeaf615_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (14, 6), with every refinement covered. -/
theorem majorization_upper_14_6 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle616 := by decide +kernel
  have h := majorizationLeaf616_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_14_6_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((14 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 14 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_14_6 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_14_6 hp)

/-- The checked actual lower triangle of cell (14, 7), with every refinement covered. -/
theorem majorization_lower_14_7 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle617 := by decide +kernel
  have h := majorizationLeaf617_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (14, 7), with every refinement covered. -/
theorem majorization_upper_14_7 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle618 := by decide +kernel
  have h := majorizationLeaf618_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_14_7_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((14 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + t) / 16)
      ((((7 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 14 7 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_14_7 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_14_7 hp)

/-- The checked actual lower triangle of cell (14, 8), with every refinement covered. -/
theorem majorization_lower_14_8 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle619 := by decide +kernel
  have h := majorizationLeaf619_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (14, 8), with every refinement covered. -/
theorem majorization_upper_14_8 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle620 := by decide +kernel
  have h := majorizationLeaf620_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_14_8_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((14 : ℕ) : ℝ) + ((8 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((14 : ℕ) : ℝ) + t) / 16)
      ((((8 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 14 8 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_14_8 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_14_8 hp)

end PartialBalayage.Maximal.Square
