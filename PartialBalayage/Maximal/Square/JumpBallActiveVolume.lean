/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpMonotoneComposition

/-!
# The actual active-volume estimate for the positive stable ball obstacle

The genuine regularized sign test makes the jump energy nonnegative. Dominated
convergence in the finite ball then gives the capped active-volume estimate from
the actual weak equation and positive-state complementarity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open PartialBalayage.Linear
open scoped RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Ω" R:arg => closedBall (0 : E) R
local notation "H" α:arg R:arg => StableJumpDirichletSpace α (Ω R)
local notation "L²" R:arg => Lp ℝ 2 (volume.restrict (Ω R))

/-- Every genuine stable weak equation has the nonnegative actual regularized pairing. -/
theorem stableJumpBall_sign_residual_nonneg (α R : ℝ) (U : H α R) (f ν : L² R)
    (hpde : ∀ W : H α R, stableJumpForm α U.val W.val =
      ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection ε (stableJumpDirichletValue α (Ω R) U x)⟫
        ∂volume.restrict (Ω R) := by
  have h := stableJumpForm_signTest_nonneg α measurableSet_closedBall hε U
  rw [hpde, L2.inner_def] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f ν,
    stableJumpDirichletSignTest_value_ae α measurableSet_closedBall hε U] with x hs ht
  simp only [hs, Pi.sub_apply, ht]

/-- Actual state positivity and cap complementarity give the true active-volume estimate. -/
theorem stableJumpBall_cap_mul_active_volume_le (α R : ℝ) (U : H α R) (f ν : L² R)
    {κ : ℝ} (hpde : ∀ W : H α R, stableJumpForm α U.val W.val =
      ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫)
    (hu : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ stableJumpDirichletValue α (Ω R) U x)
    (hcomp : ∀ᵐ x ∂volume.restrict (Ω R),
      0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) :
    κ * ((volume.restrict (Ω R))
      {x | stableJumpDirichletValue α (Ω R) U x ≠ 0}).toReal ≤
      ∫ x, ‖f x‖ ∂volume.restrict (Ω R) := by
  let : IsFiniteMeasure (volume.restrict (Ω R)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  apply cap_mul_measure_active_le_of_regularized_tests
    (Lp.aestronglyMeasurable (stableJumpDirichletValue α (Ω R) U))
    ((Lp.memLp f).integrable one_le_two) ((Lp.memLp ν).integrable one_le_two)
  · filter_upwards [hu, hcomp] with x hx hc
    rw [Real.inner_apply, Real.norm_eq_abs, abs_of_nonneg hx]
    rcases hx.eq_or_lt with hz | hp
    · rw [← hz, zero_mul, mul_zero]
    · rw [hc hp, mul_comm]
  · intro n
    exact stableJumpBall_sign_residual_nonneg α R U f ν hpde (by positivity)

set_option maxHeartbeats 600000 in
/-- The concrete positive stable ball obstacle exists with its genuine active-volume bound. -/
theorem exists_positive_stableJumpBall_obstacle_active_volume {α R : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R) (f : L² R)
    (hf : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ f x) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν : L² R) (U : H α R),
      (∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ ν x ∧ ν x ≤ κ) ∧
      (∀ᵐ x, 0 ≤ stableJumpDirichletGlobalValue α (Ω R) U x) ∧
      (∀ W : H α R, stableJumpForm α U.val W.val =
        ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫) ∧
      (∀ᵐ x ∂volume.restrict (Ω R),
        0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) ∧
      κ * ((volume.restrict (Ω R))
        {x | stableJumpDirichletValue α (Ω R) U x ≠ 0}).toReal ≤
        ∫ x, ‖f x‖ ∂volume.restrict (Ω R) := by
  obtain ⟨ν, U, hν, hu, hpde, hcomp⟩ :=
    exists_positive_stableJumpBall_obstacle hα0 hα2 hR f hf hκ
  have hus : ∀ᵐ x ∂volume.restrict (Ω R),
      0 ≤ stableJumpDirichletValue α (Ω R) U x := by
    filter_upwards [ae_restrict_of_ae hu,
      restrictL2CLM_ae (Ω R) (stableJumpDirichletGlobalValue α (Ω R) U)] with x hx he
    change stableJumpDirichletValue α (Ω R) U x = _ at he
    rw [he]
    exact hx
  exact ⟨ν, U, hν, hu, hpde, hcomp,
    stableJumpBall_cap_mul_active_volume_le α R U f ν hpde hus hcomp⟩

end PartialBalayage.Maximal.Square
