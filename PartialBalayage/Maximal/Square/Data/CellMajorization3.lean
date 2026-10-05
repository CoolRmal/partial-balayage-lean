/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves3
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

/-- The checked actual lower triangle of cell (5, 3), with every refinement covered. -/
theorem majorization_lower_5_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle261 := by decide +kernel
  have h := majorizationLeaf261_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (5, 3), with every refinement covered. -/
theorem majorization_upper_5_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle262 := by decide +kernel
  have h := majorizationLeaf262_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_5_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 5 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_3 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_5_3_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 5 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_3 hp)

/-- The checked actual lower triangle of cell (5, 4), with every refinement covered. -/
theorem majorization_lower_5_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle263 := by decide +kernel
  have h := majorizationLeaf263_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (5, 4), with every refinement covered. -/
theorem majorization_upper_5_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle264 := by decide +kernel
  have h := majorizationLeaf264_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_5_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 5 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_4 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_5_4_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 5 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_4 hp)

/-- The checked actual lower triangle of cell (5, 5), with every refinement covered. -/
theorem majorization_lower_5_5 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle265 := by decide +kernel
  have h := majorizationLeaf265_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (5, 5), with every refinement covered. -/
theorem majorization_upper_5_5 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((5 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle266 := by decide +kernel
  have h := majorizationLeaf266_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_5_5_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 5 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_5 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_5_5_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((5 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 5 5 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_5 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_5 hp)

/-- The checked actual lower triangle of cell (6, 0), with every refinement covered. -/
theorem majorization_lower_6_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle300 := by decide +kernel
  have h := majorizationLeaf300_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (6, 0), with every refinement covered. -/
theorem majorization_upper_6_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle301 := by decide +kernel
  have h := majorizationLeaf301_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_6_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((6 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 6 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_6_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_6_0 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_6_0_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((6 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 6 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_6_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_6_0 hp)

/-- The checked actual lower triangle of cell (6, 1), with every refinement covered. -/
theorem majorization_lower_6_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle302 := by decide +kernel
  have h := majorizationLeaf302_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (6, 1), with every refinement covered. -/
theorem majorization_upper_6_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle303 := by decide +kernel
  have h := majorizationLeaf303_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_6_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((6 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 6 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_6_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_6_1 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_6_1_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((6 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 6 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_6_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_6_1 hp)

/-- The checked actual lower triangle of cell (6, 2), with every refinement covered. -/
theorem majorization_lower_6_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle304 := by decide +kernel
  have h := majorizationLeaf304_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (6, 2), with every refinement covered. -/
theorem majorization_upper_6_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle305 := by decide +kernel
  have h := majorizationLeaf305_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_6_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((6 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 6 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_6_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_6_2 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_6_2_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((6 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((6 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 6 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_6_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_6_2 hp)

end PartialBalayage.Maximal.Square
