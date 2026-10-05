/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.MajorizationLeaves2
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

/-- The checked actual lower triangle of cell (4, 2), with every refinement covered. -/
theorem majorization_lower_4_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle212 := by decide +kernel
  have h := majorizationLeaf212_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (4, 2), with every refinement covered. -/
theorem majorization_upper_4_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle213 := by decide +kernel
  have h := majorizationLeaf213_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_4_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 4 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_2 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_4_2_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 4 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_2 hp)

/-- The checked actual lower triangle of cell (4, 3), with every refinement covered. -/
theorem majorization_lower_4_3 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle214 := by decide +kernel
  have h := majorizationLeaf214_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (4, 3), with every refinement covered. -/
theorem majorization_upper_4_3 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((3 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle215 := by decide +kernel
  have h := majorizationLeaf215_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_4_3_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 4 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_3 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_4_3_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((3 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 4 3 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_3 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_3 hp)

/-- The checked actual lower triangle of cell (4, 4), with every refinement covered. -/
theorem majorization_lower_4_4 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle216 := by decide +kernel
  have h := majorizationLeaf216_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (4, 4), with every refinement covered. -/
theorem majorization_upper_4_4 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + p.1) / 16)
      ((((4 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle217 := by decide +kernel
  have h := majorizationLeaf217_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_4_4_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 4 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_4 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_4_4_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((4 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((4 : ℕ) : ℝ) + t) / 16)
      ((((4 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 4 4 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_4_4 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_4_4 hp)

/-- The checked actual lower triangle of cell (5, 0), with every refinement covered. -/
theorem majorization_lower_5_0 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle255 := by decide +kernel
  have h := majorizationLeaf255_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (5, 0), with every refinement covered. -/
theorem majorization_upper_5_0 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((0 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle256 := by decide +kernel
  have h := majorizationLeaf256_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_5_0_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 5 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_0 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_5_0_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((0 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 5 0 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_0 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_0 hp)

/-- The checked actual lower triangle of cell (5, 1), with every refinement covered. -/
theorem majorization_lower_5_1 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle257 := by decide +kernel
  have h := majorizationLeaf257_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (5, 1), with every refinement covered. -/
theorem majorization_upper_5_1 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((1 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle258 := by decide +kernel
  have h := majorizationLeaf258_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_5_1_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 5 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_1 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_5_1_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((1 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 5 1 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_1 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_1 hp)

/-- The checked actual lower triangle of cell (5, 2), with every refinement covered. -/
theorem majorization_lower_5_2 {p : ℝ × ℝ} (hp : lowerCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : lowerCellTriangle = majorizationTriangle259 := by decide +kernel
  have h := majorizationLeaf259_kernel (heq ▸ hp)
  simpa using h

/-- The checked actual upper triangle of cell (5, 2), with every refinement covered. -/
theorem majorization_upper_5_2 {p : ℝ × ℝ} (hp : upperCellTriangle.Contains p) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + p.1) / 16)
      ((((2 : ℕ) : ℝ) + p.2) / 16) := by
  have heq : upperCellTriangle = majorizationTriangle260 := by decide +kernel
  have h := majorizationLeaf260_kernel (heq ▸ hp)
  simpa using h

/-- The actual kernel is nonnegative throughout the closed retained cell. -/
theorem majorization_cell_5_2_nonneg {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply kernel_nonneg_on_cell_of_triangle_bounds 5 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_2 hp)

/-- The actual kernel majorizes one throughout the closed retained cell. -/
theorem majorization_cell_5_2_one {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : ((5 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel ((((5 : ℕ) : ℝ) + t) / 16)
      ((((2 : ℕ) : ℝ) + s) / 16) := by
  apply one_le_kernel_on_cell_of_triangle_bounds 5 2 (by norm_num) ?_ ?_ ht₀ ht₁ hs₀ hs₁ hr
  · intro p hp
    exact le_trans (by norm_num) (majorization_lower_5_2 hp)
  · intro _ p hp
    exact le_trans (by norm_num) (majorization_upper_5_2 hp)

end PartialBalayage.Maximal.Square
