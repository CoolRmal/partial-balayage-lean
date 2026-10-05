/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves25
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

/-- The checked actual lower triangle of cell (17, 6), with every refinement covered. -/
theorem majorization_lower_17_6 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle690 := by decide +kernel
  have h := majorizationLeaf690_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (17, 6), with every refinement covered. -/
theorem majorization_upper_17_6 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((6 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle691 := by decide +kernel
  have h := majorizationLeaf691_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_17_6_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((17 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + t) / 16)
      ((((6 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 17 6 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_17_6 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_17_6 hp)

/-- The checked actual lower triangle of cell (17, 7), with every refinement covered. -/
theorem majorization_lower_17_7 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle692 := by decide +kernel
  have h := majorizationLeaf692_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (17, 7), with every refinement covered. -/
theorem majorization_upper_17_7 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((7 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle693 := by decide +kernel
  have h := majorizationLeaf693_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_17_7_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((17 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + t) / 16)
      ((((7 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 17 7 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_17_7 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_17_7 hp)

/-- The checked actual lower triangle of cell (17, 8), with every refinement covered. -/
theorem majorization_lower_17_8 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle694 := by decide +kernel
  have h := majorizationLeaf694_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (17, 8), with every refinement covered. -/
theorem majorization_upper_17_8 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((8 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle695 := by decide +kernel
  have h := majorizationLeaf695_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_17_8_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((17 : ℕ) : ℝ) + ((8 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + t) / 16)
      ((((8 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 17 8 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_17_8 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_17_8 hp)

/-- The checked actual lower triangle of cell (17, 9), with every refinement covered. -/
theorem majorization_lower_17_9 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((9 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle696 := by decide +kernel
  have h := majorizationLeaf696_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (17, 9), with every refinement covered. -/
theorem majorization_upper_17_9 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((9 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle697 := by decide +kernel
  have h := majorizationLeaf697_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_17_9_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((17 : ℕ) : ℝ) + ((9 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + t) / 16)
      ((((9 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 17 9 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_17_9 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_17_9 hp)

/-- The checked actual lower triangle of cell (17, 10), with every refinement covered. -/
theorem majorization_lower_17_10 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + p.1) / 16)
      ((((10 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle698 := by decide +kernel
  have h := majorizationLeaf698_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_17_10_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((17 : ℕ) : ℝ) + ((10 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((17 : ℕ) : ℝ) + t) / 16)
      ((((10 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 17 10 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_17_10 hp)
  · intro h
    omega

/-- The checked actual lower triangle of cell (18, 0), with every refinement covered. -/
theorem majorization_lower_18_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((18 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle699 := by decide +kernel
  have h := majorizationLeaf699_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (18, 0), with every refinement covered. -/
theorem majorization_upper_18_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((18 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle700 := by decide +kernel
  have h := majorizationLeaf700_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_18_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((18 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((18 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 18 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_18_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_18_0 hp)

end PartialBalayage.Maximal.Square
