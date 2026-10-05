/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves13
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

/-- The checked actual lower triangle of cell (12, 0), with every refinement covered. -/
theorem majorization_lower_12_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle543 := by decide +kernel
  have h := majorizationLeaf543_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (12, 0), with every refinement covered. -/
theorem majorization_upper_12_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle544 := by decide +kernel
  have h := majorizationLeaf544_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_12_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 12 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_0 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_12_0_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 12 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_0 hp)

/-- The checked actual lower triangle of cell (12, 1), with every refinement covered. -/
theorem majorization_lower_12_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle545 := by decide +kernel
  have h := majorizationLeaf545_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (12, 1), with every refinement covered. -/
theorem majorization_upper_12_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle546 := by decide +kernel
  have h := majorizationLeaf546_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_12_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 12 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_1 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_12_1_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 12 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_1 hp)

/-- The checked actual lower triangle of cell (12, 2), with every refinement covered. -/
theorem majorization_lower_12_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle547 := by decide +kernel
  have h := majorizationLeaf547_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (12, 2), with every refinement covered. -/
theorem majorization_upper_12_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle548 := by decide +kernel
  have h := majorizationLeaf548_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_12_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 12 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_2 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_12_2_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 12 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_2 hp)

/-- The checked actual lower triangle of cell (12, 3), with every refinement covered. -/
theorem majorization_lower_12_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle549 := by decide +kernel
  have h := majorizationLeaf549_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (12, 3), with every refinement covered. -/
theorem majorization_upper_12_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle550 := by decide +kernel
  have h := majorizationLeaf550_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_12_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 12 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_3 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_12_3_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 12 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_3 hp)
  · intro h
    omega

/-- The checked actual lower triangle of cell (12, 4), with every refinement covered. -/
theorem majorization_lower_12_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle551 := by decide +kernel
  have h := majorizationLeaf551_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (12, 4), with every refinement covered. -/
theorem majorization_upper_12_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle552 := by decide +kernel
  have h := majorizationLeaf552_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_12_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 12 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_4 hp)

/-- The checked actual lower triangle of cell (12, 5), with every refinement covered. -/
theorem majorization_lower_12_5 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle =
      majorizationTriangle553 := by decide +kernel
  have h := majorizationLeaf553_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (12, 5), with every refinement covered. -/
theorem majorization_upper_12_5 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle =
      majorizationTriangle554 := by decide +kernel
  have h := majorizationLeaf554_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_12_5_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((12 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((12 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 12 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_12_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_12_5 hp)

end PartialBalayage.Maximal.Square
