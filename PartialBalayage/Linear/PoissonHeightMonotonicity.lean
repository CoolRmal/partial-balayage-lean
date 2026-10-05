/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonQuadraticSpectral
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Actual Poisson energy increases as its height tends to zero

Convexity of the exponential compares its genuine secant slopes. This proves the actual
Poisson rate comparison and hence the monotonicity of the true spatial quadratic defects,
without any finite half-order energy assumption on the input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PartialBalayage.Linear

/-- The actual Poisson rate decreases with positive height at every real frequency. -/
theorem poissonRate_antitone_height {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hts : t ≤ s) (r : ℝ) : poissonRate s r ≤ poissonRate t r := by
  have hc : ConvexOn ℝ univ (fun x : ℝ ↦ Real.exp (-(x * r))) := by
    convert! convexOn_exp.comp_linearMap (-r • LinearMap.id : ℝ →ₗ[ℝ] ℝ) using 1
    ext x
    change Real.exp (-(x * r)) = Real.exp (-r * x)
    congr 1
    ring
  have h := hc.monotoneOn_slope_gt (mem_univ 0) ⟨mem_univ t, ht⟩ ⟨mem_univ s, hs⟩ hts
  simp only [slope_def_field, zero_mul, neg_zero, Real.exp_zero, sub_zero] at h
  rw [poissonRate, poissonRate, ite_eq_left hs, ite_eq_left ht]
  simp only [div_eq_mul_inv] at h
  nlinarith

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)

/-- The genuine spatial quadratic defect decreases with positive height. -/
theorem poissonQuadraticDefect_antitone_height {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hts : t ≤ s) (f : L²) : poissonQuadraticDefect hs f ≤ poissonQuadraticDefect ht f := by
  have h : poissonQuadraticSpectral s f ≤ poissonQuadraticSpectral t f := by
    apply lintegral_mono
    intro ξ
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (poissonRate_antitone_height ht hs hts (2 * Real.pi * ‖ξ‖)) (sq_nonneg _))
  rw [poissonQuadraticSpectral_eq_ofReal hs, poissonQuadraticSpectral_eq_ofReal ht] at h
  exact (ENNReal.ofReal_le_ofReal_iff (poissonQuadraticDefect_nonneg ht f)).mp h

end PartialBalayage.Linear
