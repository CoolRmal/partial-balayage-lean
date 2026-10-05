/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonBalayageActiveSet
public import PartialBalayage.Linear.RieszCappedEstimate
public import PartialBalayage.Linear.LinearWeakBounds

/-!
# The unconditional full-vector Riesz weak bound on every real L¹ input

Actual signed whole-space Poisson balayage constructs a capped density with
the original input mass and a controlled measurable active set. The genuine
weak equation gives full-vector Riesz cancellation off that set. The actual
L² contraction yields coefficient two at every extended-real level. The
canonical linear extension then gives the same coefficient on all real L¹.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)

/-- The full actual Riesz vector has coefficient two for every integrable real L² input. -/
theorem rieszRealL2_levelSet_bound (hn : 0 < n) (f : L²ℝ)
    (hf : Integrable (f : D → ℝ)) (α : ℝ≥0∞) :
    α * volume {x | α < ‖rieszRealL2CLM n f x‖ₑ} ≤ 2 * ∫⁻ x, ‖f x‖ₑ := by
  apply levelSet_bound_all_of_nnreal
  intro t ht
  obtain ⟨ν, U, s, hs, hcap, hν, hmass, hs_mass, hzero, hTest⟩ :=
    exists_signed_poisson_capped_decomposition hn f hf t ht
  exact riesz_levelSet_bound_of_capped_data f ν hs ht hcap hν hmass hs_mass
    (riesz_eq_off_of_Poisson_test_equations f ν U hTest hzero)

/-- The genuine full-vector Riesz map extends linearly to every real L¹ with coefficient two. -/
theorem isLinearWeakTypeBound_riesz (hn : 0 < n) :
    IsLinearWeakTypeBound (𝕜 := ℝ) (rieszRealL2CLM n) 2 := by
  have hfull : IsLinearWeakTypeBound (𝕜 := ℝ) (rieszRealL2CLM n) (ENNReal.ofReal 2) := by
    apply isLinearWeakTypeBound_of_real_L2_level_bound _ 2 (by norm_num)
    simpa only [ENNReal.ofReal_ofNat] using rieszRealL2_levelSet_bound hn
  simpa only [ENNReal.ofReal_ofNat] using hfull

/-- The actual real-input Riesz full-L¹ weak constant is at most two. -/
theorem riesz_linearWeakTypeConstant_le_two (hn : 0 < n) :
    linearWeakTypeConstant (𝕜 := ℝ) (rieszRealL2CLM n) ≤ 2 :=
  sInf_le (isLinearWeakTypeBound_riesz hn)

/-- The independently specified complete Riesz vector has the article's full-L¹ table bound. -/
theorem riesz_weakTypeConstant_le_two (n : ℕ) (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℝ) (rieszFourierOperator (n := n)) ≤ 2 := by
  have heq : (rieszFourierOperator (n := n)) = (rieszRealL2CLM n) := by
    funext f
    exact rieszFourierOperator_eq_rieszRealL2CLM f
  rw [heq]
  exact riesz_linearWeakTypeConstant_le_two (by omega)

end PartialBalayage.Linear
