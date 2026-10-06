/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.RieszLinearity
public import PartialBalayage.Linear.ExtendedLevelSet
public import PartialBalayage.Linear.CapEnergy

/-!
# The actual complex Riesz capped-density estimate

The genuine full complex Riesz vector is an L² contraction. Norm-capped complex
data, their actual mass contraction and active-set agreement give coefficient two.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)

/-- The actual full complex Riesz contraction gives coefficient two from norm-capped data. -/
theorem complex_riesz_levelSet_bound_of_capped_data (f ν : L²ℂ) {s : Set D}
    (hs : MeasurableSet s) {t : ℝ≥0} (ht : 0 < t)
    (hcap : ∀ᵐ x, ‖ν x‖ ≤ (t : ℝ)) (hν : Integrable (ν : D → ℂ))
    (hmass : (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ)
    (hs_mass : (t : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ)
    (heq : ∀ᵐ x, x ∉ s → rieszL2CLM n f x = rieszL2CLM n ν x) :
    (t : ℝ≥0∞) * volume {x | (t : ℝ≥0∞) < ‖rieszL2CLM n f x‖ₑ} ≤
      2 * ∫⁻ x, ‖f x‖ₑ := by
  have hT : eLpNorm (rieszL2CLM n ν) 2 volume ≤
      (1 : ℝ≥0∞) * eLpNorm ν 2 volume :=
    eLpNorm_le_of_Lp_norm_bound ν _ (by
      simpa only [NNReal.coe_one, one_mul, rieszL2CLM_apply] using norm_rieszL2_le ν)
  have hcap' : ∀ᵐ x, ‖ν x‖ ≤ (t / 1 : ℝ≥0) := by
    simpa only [div_one] using hcap
  have hs_mass' : ((t / 1 : ℝ≥0) : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ := by
    simpa only [div_one] using hs_mass
  simpa only [ENNReal.coe_one, mul_one] using
    levelSet_bound_two_mul_of_cap_and_L2_bound hs heq hν ht
      (by norm_num : (0 : ℝ≥0) < 1) hcap' hmass hs_mass' hT

end PartialBalayage.Linear
