/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-!
# Exact Poisson generator coefficients

The positive-height scalar difference quotient has its true isotropic rate as a uniform
upper bound and its exact limit at height zero.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PartialBalayage.Linear

/-- The actual positive-height Poisson difference-quotient coefficient. -/
def poissonRate (t r : ℝ) : ℝ :=
  if 0 < t then t⁻¹ * (1 - Real.exp (-(t * r))) else 0

/-- The exact positive-height Poisson rate is between zero and its generator frequency. -/
theorem poissonRate_bounds (t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ poissonRate t r ∧ poissonRate t r ≤ r := by
  by_cases ht : 0 < t
  · rw [poissonRate, ite_eq_left ht]
    have he : Real.exp (-(t * r)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht.le hr))
    refine ⟨mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr he), ?_⟩
    have hexp := Real.add_one_le_exp (-(t * r))
    have hdiff : 1 - Real.exp (-(t * r)) ≤ t * r := by linarith
    calc
      _ ≤ t⁻¹ * (t * r) := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr ht.le)
      _ = r := by field_simp [ht.ne']
  · simp [poissonRate, ht, hr]

/-- The actual scalar difference quotient converges to the generator frequency from the right. -/
theorem tendsto_poissonRate (r : ℝ) :
    Tendsto (fun t ↦ poissonRate t r) (𝓝[>] 0) (𝓝 r) := by
  have hd : HasDerivAt (fun t : ℝ ↦ Real.exp (-(t * r))) (-r) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).mul_const r).neg).exp using 1 <;> simp
  have hs := hd.tendsto_slope_zero_right.neg
  have heq : (fun t ↦ poissonRate t r) =ᶠ[𝓝[>] 0]
      (fun t ↦ -(t⁻¹ • (Real.exp (-((0 + t) * r)) - Real.exp (-(0 * r))))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Ioi] at ht
    rw [poissonRate, ite_eq_left ht]
    simp only [zero_add, zero_mul, neg_zero, Real.exp_zero, smul_eq_mul]
    ring
  simpa using hs.congr' heq.symm

end PartialBalayage.Linear
