/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.CellMajorization0
public import PartialBalayage.Maximal.Square.Data.CellMajorization1
public import PartialBalayage.Maximal.Square.Data.CellMajorization2
public import PartialBalayage.Maximal.Square.Data.CellMajorization3
public import PartialBalayage.Maximal.Square.Data.CellMajorization4
public import PartialBalayage.Maximal.Square.Data.CellMajorization5
public import PartialBalayage.Maximal.Square.Data.CellMajorization6
public import PartialBalayage.Maximal.Square.Data.CellMajorization7
public import PartialBalayage.Maximal.Square.Data.CellMajorization8
public import PartialBalayage.Maximal.Square.Data.CellMajorization9
public import PartialBalayage.Maximal.Square.Data.CellMajorization10
public import PartialBalayage.Maximal.Square.Data.CellMajorization11
public import PartialBalayage.Maximal.Square.Data.CellMajorization12
public import PartialBalayage.Maximal.Square.Data.CellMajorization13
public import PartialBalayage.Maximal.Square.Data.CellMajorization14
public import PartialBalayage.Maximal.Square.Data.CellMajorization15
public import PartialBalayage.Maximal.Square.Data.CellMajorization16
public import PartialBalayage.Maximal.Square.Data.CellMajorization17
public import PartialBalayage.Maximal.Square.Data.CellMajorization18
public import PartialBalayage.Maximal.Square.Data.CellMajorization19
public import PartialBalayage.Maximal.Square.Data.CellMajorization20
public import PartialBalayage.Maximal.Square.Data.CellMajorization21
public import PartialBalayage.Maximal.Square.Data.CellMajorization22
public import PartialBalayage.Maximal.Square.Data.CellMajorization23
public import PartialBalayage.Maximal.Square.Data.CellMajorization24
public import PartialBalayage.Maximal.Square.Data.CellMajorization25
public import PartialBalayage.Maximal.Square.Data.CellMajorization26
public import PartialBalayage.Maximal.Square.Data.CellMajorization27
public import PartialBalayage.Maximal.Square.Data.CellMajorization28
public import PartialBalayage.Maximal.Square.Data.CellMajorization29
public import PartialBalayage.Maximal.Square.Data.CellMajorization30
public import PartialBalayage.Maximal.Square.Data.CellMajorization31
public import PartialBalayage.Maximal.Square.Data.CellMajorization32
public import PartialBalayage.Maximal.Square.Data.CellMajorization33
public import PartialBalayage.Maximal.Square.Data.CellMajorization34

/-!
# All checked ordered grid cells

The finite cases dispatch to genuine closed-cell kernel inequalities. The opposite
half of the quarter diamond is subsequently covered by the actual kernel symmetry.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

set_option maxHeartbeats 2000000

/-- Every ordered retained grid cell has its actual nonnegative kernel. -/
theorem kernel_nonneg_on_ordered_grid (k l : ℕ) (hlk : l ≤ k) (hkl : k + l ≤ 27)
    {t s : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : (k : ℝ) + l + t + s ≤ 28) :
    (0 : ℝ) ≤ kernel (((k : ℝ) + t) / 16) (((l : ℝ) + s) / 16) := by
  have hk : k ≤ 27 := by omega
  interval_cases k
  · have hl : l ≤ 0 := by omega
    interval_cases l
    exact majorization_cell_0_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 1 := by omega
    interval_cases l
    · exact majorization_cell_1_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_1_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 2 := by omega
    interval_cases l
    · exact majorization_cell_2_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_2_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_2_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 3 := by omega
    interval_cases l
    · exact majorization_cell_3_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_3_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_3_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_3_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 4 := by omega
    interval_cases l
    · exact majorization_cell_4_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 5 := by omega
    interval_cases l
    · exact majorization_cell_5_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 6 := by omega
    interval_cases l
    · exact majorization_cell_6_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 7 := by omega
    interval_cases l
    · exact majorization_cell_7_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 8 := by omega
    interval_cases l
    · exact majorization_cell_8_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 9 := by omega
    interval_cases l
    · exact majorization_cell_9_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 10 := by omega
    interval_cases l
    · exact majorization_cell_10_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 11 := by omega
    interval_cases l
    · exact majorization_cell_11_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_11_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 12 := by omega
    interval_cases l
    · exact majorization_cell_12_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_11_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_12_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 13 := by omega
    interval_cases l
    · exact majorization_cell_13_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_11_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_12_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_13_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 13 := by omega
    interval_cases l
    · exact majorization_cell_14_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_11_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_12_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_13_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 12 := by omega
    interval_cases l
    · exact majorization_cell_15_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_11_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_15_12_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 11 := by omega
    interval_cases l
    · exact majorization_cell_16_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_16_11_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 10 := by omega
    interval_cases l
    · exact majorization_cell_17_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_17_10_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 9 := by omega
    interval_cases l
    · exact majorization_cell_18_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_18_9_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 8 := by omega
    interval_cases l
    · exact majorization_cell_19_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_19_8_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 7 := by omega
    interval_cases l
    · exact majorization_cell_20_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_20_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_20_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_20_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_20_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_20_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_20_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_20_7_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 6 := by omega
    interval_cases l
    · exact majorization_cell_21_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_21_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_21_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_21_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_21_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_21_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_21_6_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 5 := by omega
    interval_cases l
    · exact majorization_cell_22_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_22_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_22_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_22_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_22_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_22_5_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 4 := by omega
    interval_cases l
    · exact majorization_cell_23_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_23_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_23_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_23_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_23_4_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 3 := by omega
    interval_cases l
    · exact majorization_cell_24_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_24_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_24_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_24_3_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 2 := by omega
    interval_cases l
    · exact majorization_cell_25_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_25_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_25_2_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 1 := by omega
    interval_cases l
    · exact majorization_cell_26_0_nonneg ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_26_1_nonneg ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 0 := by omega
    interval_cases l
    exact majorization_cell_27_0_nonneg ht₀ ht₁ hs₀ hs₁ hr

/-- Every ordered retained grid cell has its actual unit lower bound. -/
theorem kernel_one_on_ordered_grid (k l : ℕ) (hlk : l ≤ k) (hkl : k + l ≤ 15)
    {t s : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : (k : ℝ) + l + t + s ≤ 16) :
    (1 : ℝ) ≤ kernel (((k : ℝ) + t) / 16) (((l : ℝ) + s) / 16) := by
  have hk : k ≤ 15 := by omega
  interval_cases k
  · have hl : l ≤ 0 := by omega
    interval_cases l
    exact majorization_cell_0_0_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 1 := by omega
    interval_cases l
    · exact majorization_cell_1_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_1_1_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 2 := by omega
    interval_cases l
    · exact majorization_cell_2_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_2_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_2_2_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 3 := by omega
    interval_cases l
    · exact majorization_cell_3_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_3_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_3_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_3_3_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 4 := by omega
    interval_cases l
    · exact majorization_cell_4_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_4_4_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 5 := by omega
    interval_cases l
    · exact majorization_cell_5_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_4_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_5_5_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 6 := by omega
    interval_cases l
    · exact majorization_cell_6_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_4_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_5_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_6_6_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 7 := by omega
    interval_cases l
    · exact majorization_cell_7_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_4_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_5_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_6_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_7_7_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 7 := by omega
    interval_cases l
    · exact majorization_cell_8_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_4_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_5_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_6_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_8_7_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 6 := by omega
    interval_cases l
    · exact majorization_cell_9_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_4_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_5_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_9_6_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 5 := by omega
    interval_cases l
    · exact majorization_cell_10_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_4_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_10_5_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 4 := by omega
    interval_cases l
    · exact majorization_cell_11_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_3_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_11_4_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 3 := by omega
    interval_cases l
    · exact majorization_cell_12_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_2_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_12_3_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 2 := by omega
    interval_cases l
    · exact majorization_cell_13_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_1_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_13_2_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 1 := by omega
    interval_cases l
    · exact majorization_cell_14_0_one ht₀ ht₁ hs₀ hs₁ hr
    · exact majorization_cell_14_1_one ht₀ ht₁ hs₀ hs₁ hr
  · have hl : l ≤ 0 := by omega
    interval_cases l
    exact majorization_cell_15_0_one ht₀ ht₁ hs₀ hs₁ hr

end PartialBalayage.Maximal.Square
