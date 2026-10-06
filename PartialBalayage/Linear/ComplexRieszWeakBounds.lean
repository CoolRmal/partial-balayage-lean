/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonBalayage
public import PartialBalayage.Linear.ComplexRieszCancellation
public import PartialBalayage.Linear.ComplexRieszCappedEstimate
public import PartialBalayage.Linear.WeakL1Extension
public import PartialBalayage.Linear.ComplexRieszOperatorBridge

/-!
# The unconditional complex-input full-vector Riesz coefficient two

Actual complex norm-capped Poisson balayage, physical weak-gradient cancellation
and the genuine L² contraction give every level-set bound. The canonical linear
extension then applies to every complex L¹ input with the same coefficient two.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)

/-- The actual complete Riesz vector has coefficient two on every integrable complex L² input. -/
theorem complex_rieszL2_levelSet_bound (hn : 0 < n) (f : L²ℂ)
    (hf : Integrable (f : D → ℂ)) (α : ℝ≥0∞) :
    α * volume {x | α < ‖rieszL2CLM n f x‖ₑ} ≤ 2 * ∫⁻ x, ‖f x‖ₑ := by
  apply levelSet_bound_all_of_nnreal
  intro t ht
  obtain ⟨ν, u, s, hs, hcap, hν, _, _, hmass, hs_mass, hzero, hPDE⟩ :=
    ComplexPoisson.exists_complex_poisson_capped_decomposition hn f hf t ht
  exact complex_riesz_levelSet_bound_of_capped_data f ν hs ht hcap hν hmass hs_mass
    (complex_riesz_eq_off_of_h01_equation f ν u hPDE hzero)

/-- The genuine complex Riesz map extends to every complex L¹ input with coefficient two. -/
theorem isLinearWeakTypeBound_complex_riesz (hn : 0 < n) :
    IsLinearWeakTypeBound (𝕜 := ℂ) (rieszL2CLM n) 2 := by
  simpa using
    isLinearWeakTypeBound_of_L2_level_bound (rieszL2CLM n) (2 : ℝ≥0)
      (complex_rieszL2_levelSet_bound hn)

/-- The complete actual complex-input Riesz full-L¹ weak constant is at most two. -/
theorem complex_riesz_linearWeakTypeConstant_le_two (hn : 0 < n) :
    linearWeakTypeConstant (𝕜 := ℂ) (rieszL2CLM n) ≤ 2 :=
  sInf_le (isLinearWeakTypeBound_complex_riesz hn)

/-- The independently specified complete complex Riesz vector has the full article bound. -/
theorem complex_riesz_weakTypeConstant_le_two (n : ℕ) (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (complexRieszFourierOperator (n := n)) ≤ 2 := by
  have heq : (complexRieszFourierOperator (n := n)) = (rieszL2CLM n) := by
    funext f
    exact complexRieszFourierOperator_eq_rieszL2CLM f
  rw [heq]
  exact complex_riesz_linearWeakTypeConstant_le_two (by omega)

end PartialBalayage.Linear
