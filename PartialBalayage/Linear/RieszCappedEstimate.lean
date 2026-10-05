/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.RieszLinearity
public import PartialBalayage.Linear.RieszWeakGradient
public import PartialBalayage.Linear.ExtendedLevelSet
public import PartialBalayage.Linear.CapEnergy

/-!
# Actual Riesz cancellation and the capped-density estimate

Genuine Poisson test equations identify the full Riesz vector of the removed
data with a physical gradient. Its true zero-set locality gives agreement off
the state support. The real-input L² contraction supplies the exact capped
level-set estimate with coefficient two. Construction of the whole-space
capped density and its active-volume bound is a separate requirement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "WholeState" => IsotropicDirichletState (univ : Set D)

/-- Actual Poisson tests give full-vector Riesz agreement wherever the true state vanishes. -/
theorem riesz_eq_off_of_Poisson_test_equations (f ν : L²ℝ) (U : WholeState)
    (hTest : ∀ g : L²ℝ, isotropicDirichletForm univ U
      (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) g) =
        inner ℝ (f - ν) (poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) g))
    {s : Set D} (hzero : ∀ᵐ x, x ∉ s → isotropicDirichletGlobalValue univ U x = 0) :
    ∀ᵐ x, x ∉ s → rieszRealL2CLM n f x = rieszRealL2CLM n ν x := by
  have hz := ae_rieszL2_eq_zero_of_Poisson_test_equations U (f - ν) hTest
  change ∀ᵐ x, isotropicDirichletGlobalValue univ U x = 0 →
    rieszRealL2CLM n (f - ν) x = 0 at hz
  rw [map_sub] at hz
  filter_upwards [hz, hzero,
    Lp.coeFn_sub (rieszRealL2CLM n f) (rieszRealL2CLM n ν)] with x hz hu hs
  intro hx
  exact sub_eq_zero.mp (hs.symm.trans (hz (hu hx)))

/-- The actual full-vector Riesz contraction gives coefficient two from genuine capped data. -/
theorem riesz_levelSet_bound_of_capped_data (f ν : L²ℝ) {s : Set D}
    (hs : MeasurableSet s) {t : ℝ≥0} (ht : 0 < t)
    (hcap : ∀ᵐ x, ‖ν x‖ ≤ (t : ℝ)) (hν : Integrable (ν : D → ℝ))
    (hmass : (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ)
    (hs_mass : (t : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ)
    (heq : ∀ᵐ x, x ∉ s → rieszRealL2CLM n f x = rieszRealL2CLM n ν x) :
    (t : ℝ≥0∞) * volume {x | (t : ℝ≥0∞) < ‖rieszRealL2CLM n f x‖ₑ} ≤
      2 * ∫⁻ x, ‖f x‖ₑ := by
  have hT : eLpNorm (rieszRealL2CLM n ν) 2 volume ≤
      (1 : ℝ≥0∞) * eLpNorm ν 2 volume :=
    eLpNorm_le_of_Lp_norm_bound ν _ (by
      simpa only [NNReal.coe_one, one_mul] using norm_rieszRealL2CLM_le ν)
  have hcap' : ∀ᵐ x, ‖ν x‖ ≤ (t / 1 : ℝ≥0) := by
    simpa only [div_one] using hcap
  have hs_mass' : ((t / 1 : ℝ≥0) : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ := by
    simpa only [div_one] using hs_mass
  simpa only [ENNReal.coe_one, mul_one] using
    levelSet_bound_two_mul_of_cap_and_L2_bound hs heq hν ht
      (by norm_num : (0 : ℝ≥0) < 1) hcap' hmass hs_mass' hT

end PartialBalayage.Linear
