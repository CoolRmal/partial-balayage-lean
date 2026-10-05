/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# Exact optimization of the linear-operator coefficients

This file proves scalar identities and minimization results for the coefficients in the article
*Two partial balayage principles*. It makes no assertion about the weak type bounds of operators.

The Hessian objective is minimized by its positive stationary point. Subtracting the objective at
that point factors as a nonnegative square times a positive rational expression. The projection
objective has the same structure, with a unique root of a strictly increasing cubic.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage

/-- The positive stationary parameter for the full Hessian coefficient in dimension `n`. -/
def hessianParameter (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) /
    ((n : ℝ) + 1 + Real.sqrt (((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2))))

/-- The scalar coefficient `1/a + (n-1)a/(n-a²)`, used for `0 < a < √n`. -/
def hessianCoefficient (n : ℕ) (a : ℝ) : ℝ :=
  1 / a + ((n : ℝ) - 1) * a / ((n : ℝ) - a ^ 2)

private theorem hessian_denominator_pos_aux {n : ℕ} (hn : 2 ≤ n) :
    0 < (n : ℝ) + 1 + Real.sqrt (((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sqrt_nonneg (((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2))
  linarith

/-- The prescribed Hessian parameter is positive in every dimension at least two. -/
theorem hessianParameter_pos {n : ℕ} (hn : 2 ≤ n) : 0 < hessianParameter n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact Real.sqrt_pos.mpr (div_pos (by positivity) (hessian_denominator_pos_aux hn))

/-- The square of the prescribed parameter has the rationalized quadratic-root expression. -/
theorem hessianParameter_sq {n : ℕ} (hn : 2 ≤ n) :
    hessianParameter n ^ 2 = 2 * (n : ℝ) /
      ((n : ℝ) + 1 + Real.sqrt (((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact Real.sq_sqrt (le_of_lt (div_pos (by positivity) (hessian_denominator_pos_aux hn)))

/-- The prescribed Hessian parameter belongs to the interval on which the estimate is valid. -/
theorem hessianParameter_lt_sqrt {n : ℕ} (hn : 2 ≤ n) :
    hessianParameter n < Real.sqrt n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sqrt_nonneg (((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2))
  apply Real.sqrt_lt_sqrt (by positivity)
  apply (div_lt_iff₀ (hessian_denominator_pos_aux hn)).mpr
  nlinarith

/-- The parameter solves the stationary quartic for the Hessian coefficient. -/
theorem hessianParameter_stationary {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) - 2) * hessianParameter n ^ 4 +
      (n : ℝ) * ((n : ℝ) + 1) * hessianParameter n ^ 2 - (n : ℝ) ^ 2 = 0 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt
    (show 0 ≤ ((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2) by positivity)
  rw [mul_comm 4] at hs
  rw [show hessianParameter n ^ 4 = (hessianParameter n ^ 2) ^ 2 by ring,
    hessianParameter_sq hn]
  field_simp [ne_of_gt (hessian_denominator_pos_aux hn)]
  linear_combination -(n : ℝ) ^ 2 * hs

private theorem hessianCoefficient_sub_aux {n : ℕ} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hna : (n : ℝ) - a ^ 2 ≠ 0)
    (hnb : (n : ℝ) - b ^ 2 ≠ 0)
    (hp : ((n : ℝ) - 2) * a ^ 4 + (n : ℝ) * ((n : ℝ) + 1) * a ^ 2 -
      (n : ℝ) ^ 2 = 0) :
    hessianCoefficient n b - hessianCoefficient n a =
      (b - a) ^ 2 * ((((n : ℝ) - 2) * a ^ 2 + n) * (b + a) +
        (n : ℝ) * ((n : ℝ) - 1) * a) /
        (a * b * ((n : ℝ) - b ^ 2) * ((n : ℝ) - a ^ 2)) := by
  unfold hessianCoefficient
  field_simp
  linear_combination (b - a) * hp

/-- The positive stationary point globally minimizes the Hessian objective on `(0, √n)`. -/
theorem hessianCoefficient_min {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hna : a < Real.sqrt n) (hb : 0 < b) (hnb : b < Real.sqrt n)
    (hp : ((n : ℝ) - 2) * a ^ 4 + (n : ℝ) * ((n : ℝ) + 1) * a ^ 2 -
      (n : ℝ) ^ 2 = 0) : hessianCoefficient n a ≤ hessianCoefficient n b := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hna' : 0 < (n : ℝ) - a ^ 2 := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hnb' : 0 < (n : ℝ) - b ^ 2 := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have heq := hessianCoefficient_sub_aux (ne_of_gt ha) (ne_of_gt hb)
    (ne_of_gt hna') (ne_of_gt hnb') hp
  have hn2 : (0 : ℝ) ≤ n - 2 := by linarith
  have hn1 : (0 : ℝ) ≤ n - 1 := by linarith
  have hfactor : 0 ≤ (((n : ℝ) - 2) * a ^ 2 + n) * (b + a) +
      (n : ℝ) * ((n : ℝ) - 1) * a := by positivity
  have hnonneg : 0 ≤ (b - a) ^ 2 *
      ((((n : ℝ) - 2) * a ^ 2 + n) * (b + a) + (n : ℝ) * ((n : ℝ) - 1) * a) /
      (a * b * ((n : ℝ) - b ^ 2) * ((n : ℝ) - a ^ 2)) := by positivity
  linarith

/-- Evaluating the optimized Hessian coefficient at the competitor `a = 1` gives at most two. -/
theorem hessianCoefficient_parameter_le_two {n : ℕ} (hn : 2 ≤ n) :
    hessianCoefficient n (hessianParameter n) ≤ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmin := hessianCoefficient_min hn (hessianParameter_pos hn)
    (hessianParameter_lt_sqrt hn) (by norm_num : (0 : ℝ) < 1)
    (show (1 : ℝ) < Real.sqrt n by
      exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num; linarith))
    (hessianParameter_stationary hn)
  have hone : hessianCoefficient n 1 = 2 := by
    norm_num [hessianCoefficient, ne_of_gt (show (0 : ℝ) < n - 1 by linarith)]
  simpa [hone] using hmin

/-- The prescribed Hessian coefficient is the exact infimum over the admissible interval. -/
theorem hessianCoefficient_inf {n : ℕ} (hn : 2 ≤ n) :
    sInf (hessianCoefficient n '' Set.Ioo 0 (Real.sqrt n)) =
      hessianCoefficient n (hessianParameter n) := by
  have hmem : hessianParameter n ∈ Set.Ioo 0 (Real.sqrt n) :=
    ⟨hessianParameter_pos hn, hessianParameter_lt_sqrt hn⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨hessianParameter n, hmem, rfl⟩, ?_⟩
  rintro y ⟨b, hb, rfl⟩
  exact hessianCoefficient_min hn hmem.1 hmem.2 hb.1 hb.2 (hessianParameter_stationary hn)

/-- In dimension two, the exact optimizing parameter is `√6 / 3`. -/
theorem hessianParameter_two : hessianParameter 2 = Real.sqrt 6 / 3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  simp only [hessianParameter, Nat.cast_ofNat]
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  norm_num [div_pow, hs]

/-- The optimized planar Hessian coefficient is the exact table constant `3√6 / 4`. -/
theorem hessianCoefficient_two :
    hessianCoefficient 2 (hessianParameter 2) = 3 * Real.sqrt 6 / 4 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hs0 : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [hessianParameter_two]
  simp only [hessianCoefficient, Nat.cast_ofNat]
  rw [div_pow, hs]
  field_simp
  nlinarith

/-- The cubic whose root determines the projection coefficient's minimizing parameter. -/
def projectionCubic (a : ℝ) : ℝ := a ^ 3 - 2 * a ^ 2 + 6 * a - 4

/-- The projection cubic is strictly increasing on the whole real line. -/
theorem projectionCubic_strictMono : StrictMono projectionCubic := by
  intro a b hab
  have hfactor : 0 < a ^ 2 + a * b + b ^ 2 - 2 * (a + b) + 6 := by
    nlinarith [sq_nonneg (a + b - 2), sq_nonneg a, sq_nonneg b]
  have hdiff : projectionCubic b - projectionCubic a =
      (b - a) * (a ^ 2 + a * b + b ^ 2 - 2 * (a + b) + 6) := by
    unfold projectionCubic
    ring
  have := mul_pos (sub_pos.mpr hab) hfactor
  linarith

/-- The projection cubic has exactly one zero in the open unit interval. -/
theorem existsUnique_projectionParameter :
    ∃! a : ℝ, a ∈ Set.Ioo 0 1 ∧ projectionCubic a = 0 := by
  have hcont : Continuous projectionCubic := by unfold projectionCubic; fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (projectionCubic 0) (projectionCubic 1) := by
    norm_num [projectionCubic]
  obtain ⟨a, ha, hroot⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hzero
  have ha0 : a ≠ 0 := by intro heq; subst a; norm_num [projectionCubic] at hroot
  have ha1 : a ≠ 1 := by intro heq; subst a; norm_num [projectionCubic] at hroot
  refine ⟨a, ⟨⟨lt_of_le_of_ne ha.1 (Ne.symm ha0), lt_of_le_of_ne ha.2 ha1⟩, hroot⟩, ?_⟩
  intro b hb
  exact projectionCubic_strictMono.injective (hb.2.trans hroot.symm)

/-- The unique root in `(0,1)` of `a³ - 2a² + 6a - 4 = 0`. Existence is proved above. -/
def projectionParameter : ℝ := Classical.choose existsUnique_projectionParameter

/-- The exact projection parameter is positive and less than one. -/
theorem projectionParameter_mem : projectionParameter ∈ Set.Ioo 0 1 :=
  (Classical.choose_spec existsUnique_projectionParameter).1.1

/-- The exact projection parameter satisfies the minimizing cubic. -/
theorem projectionParameter_cubic : projectionCubic projectionParameter = 0 :=
  (Classical.choose_spec existsUnique_projectionParameter).1.2

/-- The scalar coefficient `1/a + a/(2-a)²`, used for `0 < a < 2`. -/
def projectionCoefficient (a : ℝ) : ℝ := 1 / a + a / (2 - a) ^ 2

private theorem projectionCoefficient_sub_aux {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha2 : 2 - a ≠ 0) (hb2 : 2 - b ≠ 0) (hp : projectionCubic a = 0) :
    projectionCoefficient b - projectionCoefficient a =
      (b - a) ^ 2 * (4 * a + (4 - 4 * a + 2 * a ^ 2) * (2 - b)) /
        (a * b * (2 - a) ^ 2 * (2 - b) ^ 2) := by
  unfold projectionCoefficient projectionCubic at *
  field_simp
  linear_combination 2 * (b - a) * (2 - b) * hp

/-- The cubic root globally minimizes the projection objective on `(0,2)`. -/
theorem projectionCoefficient_min {a b : ℝ} (ha : a ∈ Set.Ioo 0 2)
    (hb : b ∈ Set.Ioo 0 2) (hp : projectionCubic a = 0) :
    projectionCoefficient a ≤ projectionCoefficient b := by
  have ha2 : 0 < 2 - a := sub_pos.mpr ha.2
  have hb2 : 0 < 2 - b := sub_pos.mpr hb.2
  have ha0 : 0 < a := ha.1
  have hb0 : 0 < b := hb.1
  have heq := projectionCoefficient_sub_aux (ne_of_gt ha.1) (ne_of_gt hb.1)
    (ne_of_gt ha2) (ne_of_gt hb2) hp
  have hfactor : 0 ≤ 4 - 4 * a + 2 * a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
  have hnonneg : 0 ≤ (b - a) ^ 2 * (4 * a + (4 - 4 * a + 2 * a ^ 2) * (2 - b)) /
      (a * b * (2 - a) ^ 2 * (2 - b) ^ 2) := by positivity
  linarith

/-- The exact optimized projection coefficient is the infimum over the admissible interval. -/
theorem projectionCoefficient_inf :
    sInf (projectionCoefficient '' Set.Ioo 0 2) =
      projectionCoefficient projectionParameter := by
  have hmem : projectionParameter ∈ Set.Ioo 0 2 :=
    ⟨projectionParameter_mem.1, projectionParameter_mem.2.trans (by norm_num)⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨projectionParameter, hmem, rfl⟩, ?_⟩
  rintro y ⟨b, hb, rfl⟩
  exact projectionCoefficient_min hmem hb projectionParameter_cubic

/-- Comparing the optimized projection coefficient with `a = 1` gives at most two. -/
theorem projectionCoefficient_parameter_le_two :
    projectionCoefficient projectionParameter ≤ 2 := by
  have hmem : projectionParameter ∈ Set.Ioo 0 2 :=
    ⟨projectionParameter_mem.1, projectionParameter_mem.2.trans (by norm_num)⟩
  have hmin := projectionCoefficient_min hmem
    (show (1 : ℝ) ∈ Set.Ioo 0 2 by norm_num) projectionParameter_cubic
  have hone : projectionCoefficient 1 = 2 := by norm_num [projectionCoefficient]
  simpa [hone] using hmin

end PartialBalayage
