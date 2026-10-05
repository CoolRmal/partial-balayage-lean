/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Coefficients
public import PartialBalayage.Maximal.Square.CubicSpline
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual frozen anisotropic square comparison kernel

The candidate uses the singular diamond-radius base and the exact 169 orbit spline correction.
Its value at the single origin is chosen as one; this does not affect any Lebesgue or
distributional statement. Support and symmetries follow from the real spline and integer
orbit theorems. Admissibility of its fractional generator is a separate mathematical task.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Maximal.Square

/-- The actual diamond radius in the transformed coordinates. -/
def diamondRadius (u v : ℝ) : ℝ := |u| + |v|

/-- The exact positive radial coefficient from the immutable candidate. -/
def radialCoefficient : ℝ := 11248245541992991 / 6250000000000000

/-- The exact radial support radius. -/
def supportRadius : ℝ := 7 / 4

/-- The actual truncated radial singularity, defined at zero by the standard rpow convention. -/
def radialBase (u v : ℝ) : ℝ := radialCoefficient *
  max ((diamondRadius u v) ^ (-(6 / 5 : ℝ)) - supportRadius ^ (-(6 / 5 : ℝ))) 0

/-- One exact orbit's actual tensor spline sum. -/
def orbitSpline (i j : ℕ) (u v : ℝ) : ℝ :=
  ∑ p ∈ splineOrbit i j, cubicSpline (16 * u - p.1) * cubicSpline (16 * v - p.2)

/-- The actual signed spline correction with all 1,201 tensor entries. -/
def splineCorrection (u v : ℝ) : ℝ :=
  (splineOrbits.map (fun t ↦ (t.2.2 : ℝ) * orbitSpline t.1 t.2.1 u v)).sum

/-- The actual candidate, with a harmless finite point value at its singular origin. -/
def kernel (u v : ℝ) : ℝ :=
  if u = 0 ∧ v = 0 then 1 else radialBase u v + splineCorrection u v

/-- The actual Euclidean-plane realization used by measure-theoretic comparisons. -/
def euclideanKernel (x : EuclideanSpace ℝ (Fin 2)) : ℝ := kernel (x 0) (x 1)

theorem radialCoefficient_pos : 0 < radialCoefficient := by norm_num [radialCoefficient]

theorem supportRadius_pos : 0 < supportRadius := by norm_num [supportRadius]

theorem radialBase_nonneg (u v : ℝ) : 0 ≤ radialBase u v :=
  mul_nonneg radialCoefficient_pos.le (le_max_right _ _)

/-- The genuine radial base vanishes at and beyond its stated diamond support boundary. -/
theorem radialBase_eq_zero_of_supportRadius_le {u v : ℝ}
    (h : supportRadius ≤ diamondRadius u v) : radialBase u v = 0 := by
  have hp := Real.rpow_le_rpow_of_nonpos supportRadius_pos h
    (by norm_num : -(6 / 5 : ℝ) ≤ 0)
  simp only [radialBase, max_eq_right (sub_nonpos.mpr hp), mul_zero]

/-- Every actual orbit has the representative sum of absolute real coordinate values. -/
theorem abs_sum_of_mem_splineOrbit {i j : ℕ} {a b : ℤ}
    (h : (a, b) ∈ splineOrbit i j) : |(a : ℝ)| + |(b : ℝ)| = (i : ℝ) + (j : ℝ) := by
  simp only [splineOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [abs_of_nonneg, Nat.cast_nonneg, add_comm]

/-- Each actual tensor support lies in the exact radius-7/4 diamond. -/
theorem tensorSpline_eq_zero_of_supportRadius_le {i j : ℕ} (hij : i + j + 4 ≤ 28)
    {a b : ℤ} (hab : (a, b) ∈ splineOrbit i j) {u v : ℝ}
    (h : supportRadius ≤ diamondRadius u v) :
    cubicSpline (16 * u - a) * cubicSpline (16 * v - b) = 0 := by
  by_cases hu : 2 ≤ |16 * u - (a : ℝ)|
  · rw [cubicSpline_eq_zero_of_two_le_abs hu, zero_mul]
  by_cases hv : 2 ≤ |16 * v - (b : ℝ)|
  · rw [cubicSpline_eq_zero_of_two_le_abs hv, mul_zero]
  have hu' := lt_of_not_ge hu
  have hv' := lt_of_not_ge hv
  have hau : |16 * u| ≤ |16 * u - (a : ℝ)| + |(a : ℝ)| := by
    simpa only [sub_add_cancel] using abs_add_le (16 * u - (a : ℝ)) (a : ℝ)
  have hav : |16 * v| ≤ |16 * v - (b : ℝ)| + |(b : ℝ)| := by
    simpa only [sub_add_cancel] using abs_add_le (16 * v - (b : ℝ)) (b : ℝ)
  have habs := abs_sum_of_mem_splineOrbit hab
  have hindex : (i : ℝ) + (j : ℝ) + 4 ≤ 28 := by exact_mod_cast hij
  norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)] at hau hav
  unfold supportRadius diamondRadius at h
  exfalso
  linarith

/-- Every actual orbit spline vanishes off the common support diamond. -/
theorem orbitSpline_eq_zero_of_supportRadius_le {i j : ℕ} (hij : i + j + 4 ≤ 28)
    {u v : ℝ} (h : supportRadius ≤ diamondRadius u v) : orbitSpline i j u v = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exact tensorSpline_eq_zero_of_supportRadius_le hij hp h

/-- The genuine signed spline correction vanishes at and beyond the support diamond. -/
theorem splineCorrection_eq_zero_of_supportRadius_le {u v : ℝ}
    (h : supportRadius ≤ diamondRadius u v) : splineCorrection u v = 0 := by
  unfold splineCorrection
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  rw [orbitSpline_eq_zero_of_supportRadius_le (splineOrbits_admissible t ht).2 h, mul_zero]

/-- The concrete frozen kernel vanishes at and beyond the exact support boundary. -/
theorem kernel_eq_zero_of_supportRadius_le {u v : ℝ}
    (h : supportRadius ≤ diamondRadius u v) : kernel u v = 0 := by
  have hnot : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨rfl, rfl⟩
    norm_num [supportRadius, diamondRadius] at h
  rw [kernel, ite_eq_right hnot, radialBase_eq_zero_of_supportRadius_le h,
    splineCorrection_eq_zero_of_supportRadius_le h, add_zero]

/-- Orbit summation preserves the actual coordinate-interchange symmetry. -/
theorem orbitSpline_swap (i j : ℕ) (u v : ℝ) :
    orbitSpline i j v u = orbitSpline i j u v := by
  apply Finset.sum_equiv (Equiv.prodComm ℤ ℤ)
  · intro p
    exact mem_splineOrbit_swap i j p.1 p.2
  · intro p hp
    exact mul_comm _ _

/-- Orbit summation preserves actual evenness in the first spatial coordinate. -/
theorem orbitSpline_neg_left (i j : ℕ) (u v : ℝ) :
    orbitSpline i j (-u) v = orbitSpline i j u v := by
  apply Finset.sum_nbij' (fun p : ℤ × ℤ ↦ (-p.1, p.2))
    (fun p : ℤ × ℤ ↦ (-p.1, p.2))
  · intro p hp
    exact (mem_splineOrbit_neg_left i j p.1 p.2).mp hp
  · intro p hp
    exact (mem_splineOrbit_neg_left i j p.1 p.2).mp hp
  · intro p hp
    simp
  · intro p hp
    simp
  · intro p hp
    have h : 16 * (-u) - (p.1 : ℝ) = -(16 * u - ((-p.1 : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [h, cubicSpline_neg]

/-- Orbit summation preserves actual evenness in the second spatial coordinate. -/
theorem orbitSpline_neg_right (i j : ℕ) (u v : ℝ) :
    orbitSpline i j u (-v) = orbitSpline i j u v := by
  rw [orbitSpline_swap, orbitSpline_neg_left, orbitSpline_swap]

/-- The actual correction is invariant under coordinate interchange. -/
theorem splineCorrection_swap (u v : ℝ) : splineCorrection v u = splineCorrection u v := by
  simp only [splineCorrection, orbitSpline_swap]

/-- The actual correction is even in its first spatial coordinate. -/
theorem splineCorrection_neg_left (u v : ℝ) :
    splineCorrection (-u) v = splineCorrection u v := by
  simp only [splineCorrection, orbitSpline_neg_left]

/-- The actual correction is even in its second spatial coordinate. -/
theorem splineCorrection_neg_right (u v : ℝ) :
    splineCorrection u (-v) = splineCorrection u v := by
  simp only [splineCorrection, orbitSpline_neg_right]

/-- The genuine comparison kernel is invariant under coordinate interchange. -/
theorem kernel_swap (u v : ℝ) : kernel v u = kernel u v := by
  simp only [kernel, and_comm, radialBase, diamondRadius, add_comm,
    splineCorrection_swap]

/-- The genuine comparison kernel is even in its first spatial coordinate. -/
theorem kernel_neg_left (u v : ℝ) : kernel (-u) v = kernel u v := by
  simp only [kernel, neg_eq_zero, radialBase, diamondRadius, abs_neg,
    splineCorrection_neg_left]

/-- The genuine comparison kernel is even in its second spatial coordinate. -/
theorem kernel_neg_right (u v : ℝ) : kernel u (-v) = kernel u v := by
  simp only [kernel, neg_eq_zero, radialBase, diamondRadius, abs_neg,
    splineCorrection_neg_right]

/-- The single chosen origin value satisfies both target pointwise inequalities. -/
theorem kernel_zero_zero : kernel 0 0 = 1 := by simp only [kernel, and_self, ↓reduceIte]

/-- The concrete Euclidean kernel is genuinely even. -/
theorem euclideanKernel_neg (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanKernel (-x) = euclideanKernel x := by
  simp only [euclideanKernel, PiLp.neg_apply, kernel_neg_left, kernel_neg_right]

/-- Each actual orbit spline is continuous as a function on the Euclidean plane. -/
theorem continuous_orbitSpline (i j : ℕ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ orbitSpline i j (x 0) (x 1)) := by
  unfold orbitSpline
  apply continuous_finsetSum
  intro p hp
  apply Continuous.mul <;> apply continuous_cubicSpline.comp <;> fun_prop

/-- The actual finite signed spline correction is continuous on the Euclidean plane. -/
theorem continuous_splineCorrection :
    Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ splineCorrection (x 0) (x 1)) := by
  unfold splineCorrection
  induction splineOrbits with
  | nil =>
    simpa only [List.map_nil, List.sum_nil] using
      (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin 2) ↦ (0 : ℝ)))
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((continuous_orbitSpline t.1 t.2.1).const_mul (t.2.2 : ℝ)).fun_add ih

end PartialBalayage.Maximal.Square
