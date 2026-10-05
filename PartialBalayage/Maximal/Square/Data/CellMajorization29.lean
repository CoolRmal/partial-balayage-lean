/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves29
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

/-- The checked actual lower triangle of cell (20, 0), with every refinement covered. -/
theorem majorization_lower_20_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle735 := by decide +kernel
  have h := majorizationLeaf735_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (20, 0), with every refinement covered. -/
theorem majorization_upper_20_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle736 := by decide +kernel
  have h := majorizationLeaf736_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_20_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((20 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 20 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_20_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_20_0 hp)

/-- The checked actual lower triangle of cell (20, 1), with every refinement covered. -/
theorem majorization_lower_20_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle737 := by decide +kernel
  have h := majorizationLeaf737_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (20, 1), with every refinement covered. -/
theorem majorization_upper_20_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle738 := by decide +kernel
  have h := majorizationLeaf738_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_20_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((20 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 20 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_20_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_20_1 hp)

/-- The checked actual lower triangle of cell (20, 2), with every refinement covered. -/
theorem majorization_lower_20_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle739 := by decide +kernel
  have h := majorizationLeaf739_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (20, 2), with every refinement covered. -/
theorem majorization_upper_20_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle740 := by decide +kernel
  have h := majorizationLeaf740_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_20_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((20 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 20 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_20_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_20_2 hp)

/-- The checked actual lower triangle of cell (20, 3), with every refinement covered. -/
theorem majorization_lower_20_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle741 := by decide +kernel
  have h := majorizationLeaf741_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (20, 3), with every refinement covered. -/
theorem majorization_upper_20_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle742 := by decide +kernel
  have h := majorizationLeaf742_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_20_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((20 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 20 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_20_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_20_3 hp)

/-- The checked actual lower triangle of cell (20, 4), with every refinement covered. -/
theorem majorization_lower_20_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle743 := by decide +kernel
  have h := majorizationLeaf743_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (20, 4), with every refinement covered. -/
theorem majorization_upper_20_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle744 := by decide +kernel
  have h := majorizationLeaf744_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_20_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((20 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 20 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_20_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_20_4 hp)

/-- The checked actual lower triangle of cell (20, 5), with every refinement covered. -/
theorem majorization_lower_20_5 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle745 := by decide +kernel
  have h := majorizationLeaf745_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (20, 5), with every refinement covered. -/
theorem majorization_upper_20_5 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle746 := by decide +kernel
  have h := majorizationLeaf746_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_20_5_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((20 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((20 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 20 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_20_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_20_5 hp)

end PartialBalayage.Maximal.Square
