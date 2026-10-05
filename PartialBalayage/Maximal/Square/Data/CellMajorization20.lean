/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves20
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

/-- The checked actual lower triangle of cell (15, 1), with every refinement covered. -/
theorem majorization_lower_15_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle632 := by decide +kernel
  have h := majorizationLeaf632_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (15, 1), with every refinement covered. -/
theorem majorization_upper_15_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle633 := by decide +kernel
  have h := majorizationLeaf633_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_15_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((15 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 15 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_15_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_15_1 hp)

/-- The checked actual lower triangle of cell (15, 2), with every refinement covered. -/
theorem majorization_lower_15_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle634 := by decide +kernel
  have h := majorizationLeaf634_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (15, 2), with every refinement covered. -/
theorem majorization_upper_15_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle635 := by decide +kernel
  have h := majorizationLeaf635_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_15_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((15 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 15 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_15_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_15_2 hp)

/-- The checked actual lower triangle of cell (15, 3), with every refinement covered. -/
theorem majorization_lower_15_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle636 := by decide +kernel
  have h := majorizationLeaf636_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (15, 3), with every refinement covered. -/
theorem majorization_upper_15_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle637 := by decide +kernel
  have h := majorizationLeaf637_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_15_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((15 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 15 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_15_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_15_3 hp)

/-- The checked actual lower triangle of cell (15, 4), with every refinement covered. -/
theorem majorization_lower_15_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle638 := by decide +kernel
  have h := majorizationLeaf638_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (15, 4), with every refinement covered. -/
theorem majorization_upper_15_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle639 := by decide +kernel
  have h := majorizationLeaf639_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_15_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((15 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 15 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_15_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_15_4 hp)

/-- The checked actual lower triangle of cell (15, 5), with every refinement covered. -/
theorem majorization_lower_15_5 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle640 := by decide +kernel
  have h := majorizationLeaf640_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (15, 5), with every refinement covered. -/
theorem majorization_upper_15_5 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle641 := by decide +kernel
  have h := majorizationLeaf641_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_15_5_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((15 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 15 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_15_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_15_5 hp)

/-- The checked actual lower triangle of cell (15, 6), with every refinement covered. -/
theorem majorization_lower_15_6 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle642 := by decide +kernel
  have h := majorizationLeaf642_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (15, 6), with every refinement covered. -/
theorem majorization_upper_15_6 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle643 := by decide +kernel
  have h := majorizationLeaf643_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_15_6_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((15 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((15 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 15 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_15_6 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_15_6 hp)

end PartialBalayage.Maximal.Square
