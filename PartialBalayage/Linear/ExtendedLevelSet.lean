/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CapEnergy

/-!
# All extended-real levels and actual L² operator norms

A proved estimate at every positive finite level covers zero and infinite levels too.
Actual L² norm bounds give the same extended-real seminorm bounds used in the cap argument.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {μ : Measure X}

/-- Genuine positive finite level bounds include every extended-real level. -/
theorem levelSet_bound_all_of_nnreal (G : X → E) (Cmass : ℝ≥0∞)
    (hb : ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖G x‖ₑ} ≤ Cmass) (α : ℝ≥0∞) :
    α * μ {x | α < ‖G x‖ₑ} ≤ Cmass := by
  by_cases h0 : α = 0
  · simp only [h0, zero_mul, zero_le]
  by_cases htop : α = ⊤
  · simp only [htop, not_top_lt, ofPred_false, measure_empty, mul_zero, zero_le]
  have heq : (α.toNNReal : ℝ≥0∞) = α := ENNReal.coe_toNNReal htop
  have hpos : 0 < α.toNNReal := by
    apply pos_iff_ne_zero.mpr
    intro h
    apply h0
    rw [← heq, h, ENNReal.coe_zero]
  simpa only [heq] using hb α.toNNReal hpos

/-- An actual L² operator norm bound is the exact extended-real seminorm estimate. -/
theorem eLpNorm_le_of_Lp_norm_bound (f : Lp E 2 μ) (g : Lp F 2 μ) {M : ℝ≥0}
    (h : ‖g‖ ≤ (M : ℝ) * ‖f‖) :
    eLpNorm g 2 μ ≤ (M : ℝ≥0∞) * eLpNorm f 2 μ := by
  have hnn : ‖g‖₊ ≤ M * ‖f‖₊ := by exact_mod_cast h
  simpa only [← Lp.enorm_def, enorm, ← ENNReal.coe_mul] using
    ENNReal.coe_le_coe.mpr hnn

end PartialBalayage.Linear
