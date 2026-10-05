/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelMajorization
public import PartialBalayage.Maximal.Square.RadialGeneratorDefinitions

/-!
# Actual generator positivity beyond the square kernel support

The genuine full kernel is nonnegative and vanishes at the support boundary
and outside it. Every actual coordinate second difference is consequently
nonnegative there, including all signed spline corrections together.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- A genuine nonnegative kernel has a nonnegative coordinate generator at its zero points. -/
theorem coordinateStableGenerator_nonneg_of_eq_zero {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ} (hK : ∀ y, 0 ≤ K y)
    {x : E} (hx : K x = 0) : 0 ≤ coordinateStableGenerator α K x := by
  unfold coordinateStableGenerator
  apply mul_nonneg (stableNormalization_pos hα0 hα2).le
  apply Finset.sum_nonneg
  intro i _
  unfold stableGeneratorIntegral
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [stableSecondDifference, coordinateLine, zero_smul, add_zero, hx,
    smul_eq_mul, mul_zero, sub_zero]
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (add_nonneg (hK _) (hK _))

/-- The actual full square kernel generator is nonnegative at and beyond its support. -/
theorem coordinateStableGenerator_euclideanKernel_nonneg_exterior (x : E)
    (hx : supportRadius ≤ diamondRadius (x 0) (x 1)) :
    0 ≤ coordinateStableGenerator (6 / 5) euclideanKernel x := by
  apply coordinateStableGenerator_nonneg_of_eq_zero (by norm_num) (by norm_num)
    euclideanKernel_nonneg
  exact kernel_eq_zero_of_supportRadius_le hx

end PartialBalayage.Maximal.Square
