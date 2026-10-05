/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves31
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

/-- The checked actual lower triangle of cell (21, 4), with every refinement covered. -/
theorem majorization_lower_21_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle758 := by decide +kernel
  have h := majorizationLeaf758_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (21, 4), with every refinement covered. -/
theorem majorization_upper_21_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle759 := by decide +kernel
  have h := majorizationLeaf759_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_21_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((21 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 21 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_21_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_21_4 hp)

/-- The checked actual lower triangle of cell (21, 5), with every refinement covered. -/
theorem majorization_lower_21_5 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle760 := by decide +kernel
  have h := majorizationLeaf760_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (21, 5), with every refinement covered. -/
theorem majorization_upper_21_5 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle761 := by decide +kernel
  have h := majorizationLeaf761_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_21_5_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((21 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 21 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_21_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_21_5 hp)

/-- The checked actual lower triangle of cell (21, 6), with every refinement covered. -/
theorem majorization_lower_21_6 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle762 := by decide +kernel
  have h := majorizationLeaf762_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_21_6_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((21 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((21 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 21 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_21_6 hp)
  · intro h
    omega

/-- The checked actual lower triangle of cell (22, 0), with every refinement covered. -/
theorem majorization_lower_22_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle763 := by decide +kernel
  have h := majorizationLeaf763_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (22, 0), with every refinement covered. -/
theorem majorization_upper_22_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle764 := by decide +kernel
  have h := majorizationLeaf764_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_22_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((22 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 22 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_22_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_22_0 hp)

/-- The checked actual lower triangle of cell (22, 1), with every refinement covered. -/
theorem majorization_lower_22_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle765 := by decide +kernel
  have h := majorizationLeaf765_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (22, 1), with every refinement covered. -/
theorem majorization_upper_22_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle766 := by decide +kernel
  have h := majorizationLeaf766_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_22_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((22 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 22 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_22_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_22_1 hp)

/-- The checked actual lower triangle of cell (22, 2), with every refinement covered. -/
theorem majorization_lower_22_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle767 := by decide +kernel
  have h := majorizationLeaf767_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (22, 2), with every refinement covered. -/
theorem majorization_upper_22_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle768 := by decide +kernel
  have h := majorizationLeaf768_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_22_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((22 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((22 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 22 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_22_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_22_2 hp)

end PartialBalayage.Maximal.Square
