/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves7
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

/-- The checked actual lower triangle of cell (8, 6), with every refinement covered. -/
theorem majorization_lower_8_6 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle396 := by decide +kernel
  have h := majorizationLeaf396_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (8, 6), with every refinement covered. -/
theorem majorization_upper_8_6 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle397 := by decide +kernel
  have h := majorizationLeaf397_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_8_6_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((8 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 8 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_8_6 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_8_6 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_8_6_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((8 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 8 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_8_6 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_8_6 hp)

/-- The checked actual lower triangle of cell (8, 7), with every refinement covered. -/
theorem majorization_lower_8_7 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle398 := by decide +kernel
  have h := majorizationLeaf398_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (8, 7), with every refinement covered. -/
theorem majorization_upper_8_7 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle399 := by decide +kernel
  have h := majorizationLeaf399_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_8_7_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((8 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + t) / 16)
      ((((7 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 8 7 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_8_7 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_8_7 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_8_7_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((8 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + t) / 16)
      ((((7 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 8 7 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_8_7 hp)
  · intro h
    omega

/-- The checked actual lower triangle of cell (8, 8), with every refinement covered. -/
theorem majorization_lower_8_8 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle400 := by decide +kernel
  have h := majorizationLeaf400_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (8, 8), with every refinement covered. -/
theorem majorization_upper_8_8 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle401 := by decide +kernel
  have h := majorizationLeaf401_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_8_8_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((8 : ℕ) : ℝ) + ((8 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((8 : ℕ) : ℝ) + t) / 16)
      ((((8 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 8 8 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_8_8 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_8_8 hp)

/-- The checked actual lower triangle of cell (9, 0), with every refinement covered. -/
theorem majorization_lower_9_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle423 := by decide +kernel
  have h := majorizationLeaf423_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 0), with every refinement covered. -/
theorem majorization_upper_9_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle424 := by decide +kernel
  have h := majorizationLeaf424_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_0 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_9_0_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 9 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_0 hp)

/-- The checked actual lower triangle of cell (9, 1), with every refinement covered. -/
theorem majorization_lower_9_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle425 := by decide +kernel
  have h := majorizationLeaf425_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 1), with every refinement covered. -/
theorem majorization_upper_9_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle426 := by decide +kernel
  have h := majorizationLeaf426_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_1 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_9_1_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 9 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_1 hp)

/-- The checked actual lower triangle of cell (9, 2), with every refinement covered. -/
theorem majorization_lower_9_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle427 := by decide +kernel
  have h := majorizationLeaf427_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 2), with every refinement covered. -/
theorem majorization_upper_9_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle428 := by decide +kernel
  have h := majorizationLeaf428_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_2 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_9_2_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 9 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_2 hp)

end PartialBalayage.Maximal.Square
