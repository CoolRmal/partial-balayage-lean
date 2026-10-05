/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves1
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

/-- The checked actual lower triangle of cell (3, 0), with every refinement covered. -/
theorem majorization_lower_3_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle159 := by decide +kernel
  have h := majorizationLeaf159_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (3, 0), with every refinement covered. -/
theorem majorization_upper_3_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle160 := by decide +kernel
  have h := majorizationLeaf160_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_3_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 3 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_0 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_3_0_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 3 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_0 hp)

/-- The checked actual lower triangle of cell (3, 1), with every refinement covered. -/
theorem majorization_lower_3_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle161 := by decide +kernel
  have h := majorizationLeaf161_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (3, 1), with every refinement covered. -/
theorem majorization_upper_3_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle162 := by decide +kernel
  have h := majorizationLeaf162_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_3_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 3 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_1 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_3_1_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 3 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_1 hp)

/-- The checked actual lower triangle of cell (3, 2), with every refinement covered. -/
theorem majorization_lower_3_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle163 := by decide +kernel
  have h := majorizationLeaf163_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (3, 2), with every refinement covered. -/
theorem majorization_upper_3_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle164 := by decide +kernel
  have h := majorizationLeaf164_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_3_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 3 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_2 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_3_2_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 3 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_2 hp)

/-- The checked actual lower triangle of cell (3, 3), with every refinement covered. -/
theorem majorization_lower_3_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle165 := by decide +kernel
  have h := majorizationLeaf165_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (3, 3), with every refinement covered. -/
theorem majorization_upper_3_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle166 := by decide +kernel
  have h := majorizationLeaf166_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_3_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 3 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_3 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_3_3_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((3 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((3 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 3 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_3_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_3_3 hp)

/-- The checked actual lower triangle of cell (4, 0), with every refinement covered. -/
theorem majorization_lower_4_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle208 := by decide +kernel
  have h := majorizationLeaf208_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (4, 0), with every refinement covered. -/
theorem majorization_upper_4_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle209 := by decide +kernel
  have h := majorizationLeaf209_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_4_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 4 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_0 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_4_0_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 4 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_0 hp)

/-- The checked actual lower triangle of cell (4, 1), with every refinement covered. -/
theorem majorization_lower_4_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle210 := by decide +kernel
  have h := majorizationLeaf210_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (4, 1), with every refinement covered. -/
theorem majorization_upper_4_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle211 := by decide +kernel
  have h := majorizationLeaf211_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_4_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 4 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_1 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_4_1_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 4 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_1 hp)

end PartialBalayage.Maximal.Square
