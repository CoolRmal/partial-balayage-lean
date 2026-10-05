/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.OrderedGridMajorization

/-!
# Global nonnegativity and diamond majorization of the actual kernel

All coefficient, power, Bernstein, and coverage checks have been discharged in Lean.
Reflection and interchange symmetry extend the checked quarter-grid inequalities to
every actual point of the plane, including the origin and both diamond boundaries.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Reflection symmetry identifies the actual kernel at the absolute coordinates. -/
theorem kernel_abs (u v : ℝ) : kernel |u| |v| = kernel u v := by
  by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hu, abs_of_nonneg hv]
  · rw [abs_of_nonneg hu, abs_of_neg (by linarith), kernel_neg_right]
  · rw [abs_of_neg (by linarith), abs_of_nonneg hv, kernel_neg_left]
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith), kernel_neg_left,
      kernel_neg_right]

/-- The checked actual quarter-grid and exact support cover every nonnegative pair. -/
theorem kernel_nonneg_quarter {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ kernel u v := by
  by_cases hR : supportRadius ≤ diamondRadius u v
  · rw [kernel_eq_zero_of_supportRadius_le hR]
  have hr : u + v ≤ 7 / 4 := by
    have h := (lt_of_not_ge hR).le
    simpa only [diamondRadius, abs_of_nonneg hu, abs_of_nonneg hv, supportRadius] using h
  obtain ⟨k, l, hkl, t, s, ht₀, ht₁, hs₀, hs₁, hueq, hveq⟩ :=
    exists_closed_quarter_grid hu hv hr
  have hrad : (k : ℝ) + l + t + s ≤ 28 := by rw [hueq, hveq] at hr; linarith
  rw [hueq, hveq]
  by_cases hlk : l ≤ k
  · exact kernel_nonneg_on_ordered_grid k l hlk hkl ht₀ ht₁ hs₀ hs₁ hrad
  have h := kernel_nonneg_on_ordered_grid l k (by omega) (by omega)
    hs₀ hs₁ ht₀ ht₁ (by linarith : (l : ℝ) + k + s + t ≤ 28)
  rw [kernel_swap] at h
  exact h

/-- The actual 1,201-coefficient kernel is nonnegative at every point of the plane. -/
theorem kernel_nonneg (u v : ℝ) : 0 ≤ kernel u v := by
  rw [← kernel_abs u v]
  exact kernel_nonneg_quarter (abs_nonneg u) (abs_nonneg v)

/-- The closed unit quarter diamond is covered by actual checked unit-bound cells. -/
theorem one_le_kernel_quarter {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : u + v ≤ 1) : 1 ≤ kernel u v := by
  obtain ⟨k, l, hkl, t, s, ht₀, ht₁, hs₀, hs₁, hueq, hveq⟩ :=
    exists_closed_unit_diamond_grid hu hv hr
  have hrad : (k : ℝ) + l + t + s ≤ 16 := by rw [hueq, hveq] at hr; linarith
  rw [hueq, hveq]
  by_cases hlk : l ≤ k
  · exact kernel_one_on_ordered_grid k l hlk hkl ht₀ ht₁ hs₀ hs₁ hrad
  have h := kernel_one_on_ordered_grid l k (by omega) (by omega)
    hs₀ hs₁ ht₀ ht₁ (by linarith : (l : ℝ) + k + s + t ≤ 16)
  rw [kernel_swap] at h
  exact h

/-- The actual kernel majorizes the indicator of the entire closed unit diamond. -/
theorem one_le_kernel_of_diamondRadius_le_one {u v : ℝ}
    (hr : diamondRadius u v ≤ 1) : 1 ≤ kernel u v := by
  rw [← kernel_abs u v]
  exact one_le_kernel_quarter (abs_nonneg u) (abs_nonneg v) hr

/-- The actual Euclidean-plane kernel is nonnegative everywhere. -/
theorem euclideanKernel_nonneg (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ euclideanKernel x := kernel_nonneg (x 0) (x 1)

/-- The actual Euclidean kernel majorizes one on the closed unit diamond. -/
theorem one_le_euclideanKernel_of_diamond {x : EuclideanSpace ℝ (Fin 2)}
    (hx : |x 0| + |x 1| ≤ 1) : 1 ≤ euclideanKernel x :=
  one_le_kernel_of_diamondRadius_le_one hx

/-- The genuine closed-diamond indicator is bounded by the actual Euclidean kernel. -/
theorem indicator_diamond_le_euclideanKernel (x : EuclideanSpace ℝ (Fin 2)) :
    Set.indicator {y : EuclideanSpace ℝ (Fin 2) | |y 0| + |y 1| ≤ 1}
      (fun _ ↦ (1 : ℝ)) x ≤ euclideanKernel x := by
  classical
  simp only [Set.indicator_apply]
  split_ifs with hx
  · exact one_le_euclideanKernel_of_diamond hx
  · exact euclideanKernel_nonneg x

end PartialBalayage.Maximal.Square
