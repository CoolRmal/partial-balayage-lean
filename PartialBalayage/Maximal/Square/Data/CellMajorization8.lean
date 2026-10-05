/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves8
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

/-- The checked actual lower triangle of cell (9, 3), with every refinement covered. -/
theorem majorization_lower_9_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle429 := by decide +kernel
  have h := majorizationLeaf429_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 3), with every refinement covered. -/
theorem majorization_upper_9_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle430 := by decide +kernel
  have h := majorizationLeaf430_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_3 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_9_3_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 9 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_3 hp)

/-- The checked actual lower triangle of cell (9, 4), with every refinement covered. -/
theorem majorization_lower_9_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle431 := by decide +kernel
  have h := majorizationLeaf431_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 4), with every refinement covered. -/
theorem majorization_upper_9_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle432 := by decide +kernel
  have h := majorizationLeaf432_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_4 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_9_4_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 9 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_4 hp)

/-- The checked actual lower triangle of cell (9, 5), with every refinement covered. -/
theorem majorization_lower_9_5 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle433 := by decide +kernel
  have h := majorizationLeaf433_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 5), with every refinement covered. -/
theorem majorization_upper_9_5 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle434 := by decide +kernel
  have h := majorizationLeaf434_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_5_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_5 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_9_5_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 9 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_5 hp)

/-- The checked actual lower triangle of cell (9, 6), with every refinement covered. -/
theorem majorization_lower_9_6 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle435 := by decide +kernel
  have h := majorizationLeaf435_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 6), with every refinement covered. -/
theorem majorization_upper_9_6 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle436 := by decide +kernel
  have h := majorizationLeaf436_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_6_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_6 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_6 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_9_6_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 9 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_6 hp)
  · intro h
    omega

/-- The checked actual lower triangle of cell (9, 7), with every refinement covered. -/
theorem majorization_lower_9_7 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle437 := by decide +kernel
  have h := majorizationLeaf437_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 7), with every refinement covered. -/
theorem majorization_upper_9_7 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle438 := by decide +kernel
  have h := majorizationLeaf438_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_7_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((7 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 7 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_7 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_7 hp)

/-- The checked actual lower triangle of cell (9, 8), with every refinement covered. -/
theorem majorization_lower_9_8 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle439 := by decide +kernel
  have h := majorizationLeaf439_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (9, 8), with every refinement covered. -/
theorem majorization_upper_9_8 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle440 := by decide +kernel
  have h := majorizationLeaf440_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_9_8_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((9 : ℕ) : ℝ) + ((8 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((9 : ℕ) : ℝ) + t) / 16)
      ((((8 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 9 8 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_9_8 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_9_8 hp)

end PartialBalayage.Maximal.Square
