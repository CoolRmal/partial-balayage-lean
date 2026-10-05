/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonWholeSpaceBalayage

/-!
# Actual measurable active sets for signed Poisson balayage

The genuine signed state's active set has a measurable cover with exactly the same measure.
Actual cap saturation bounds its cap-weighted volume by the true full density mass, which
the constructed signed obstacle bounds by input mass. The actual state vanishes outside
this cover, giving the precise support needed for full-vector Riesz cancellation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace NNReal ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "WholeState" => IsotropicDirichletState (univ : Set D)

/-- The actual measurable cover of the true signed half-order state's active set. -/
def poissonBalayageActiveSet (U : WholeState) : Set D :=
  toMeasurable volume {x | isotropicDirichletGlobalValue univ U x ≠ 0}

theorem measurableSet_poissonBalayageActiveSet (U : WholeState) :
    MeasurableSet (poissonBalayageActiveSet U) := measurableSet_toMeasurable _ _

/-- The genuine state vanishes pointwise outside the actual measurable active cover. -/
theorem poissonGlobalValue_eq_zero_off_activeSet (U : WholeState) {x : D}
    (hx : x ∉ poissonBalayageActiveSet U) : isotropicDirichletGlobalValue univ U x = 0 := by
  by_contra hn
  exact hx (subset_toMeasurable volume _ hn)

/-- Actual cap saturation controls active volume by the genuine full density mass. -/
theorem cap_measure_poissonBalayageActiveSet (U : WholeState) (ν : L²ℝ) (κ : ℝ≥0)
    (hsat : ∀ᵐ x, isotropicDirichletGlobalValue univ U x ≠ 0 → ‖ν x‖ = (κ : ℝ)) :
    (κ : ℝ≥0∞) * volume (poissonBalayageActiveSet U) ≤ ∫⁻ x, ‖ν x‖ₑ := by
  let s : Set D := {x | isotropicDirichletGlobalValue univ U x ≠ 0}
  have hs : NullMeasurableSet s volume := by
    have hu := Lp.aestronglyMeasurable (isotropicDirichletGlobalValue univ U)
    have hz := hu.norm.nullMeasurableSet_eq_fun
      (aestronglyMeasurable_const (b := (0 : ℝ)))
    simpa only [s, norm_eq_zero, Set.compl_ofPred] using hz.compl
  have hle : ∫⁻ x, s.indicator (fun _ ↦ (κ : ℝ≥0∞)) x ≤ ∫⁻ x, ‖ν x‖ₑ := by
    apply lintegral_mono_ae
    filter_upwards [hsat] with x hx
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs, ← ofReal_norm, hx hxs, ENNReal.ofReal_coe_nnreal]
    · rw [indicator_of_notMem hxs]
      exact zero_le
  rw [lintegral_indicator₀ hs, lintegral_const, Measure.restrict_apply_univ] at hle
  simpa only [poissonBalayageActiveSet, measure_toMeasurable, s] using hle

/-- The genuine norm-and-mass constraint with actual input mass gives true mass contraction. -/
theorem lintegral_norm_le_input_of_poisson_mass_cap (f ν : L²ℝ)
    (hf : Integrable (f : D → ℝ)) (κ : ℝ≥0)
    (hν : ν ∈ normMassCap volume κ
      ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩) :
    (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_of_mem_normMassCap hν),
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  exact ENNReal.ofReal_le_ofReal (integral_norm_le_of_mem_normMassCap hν)

/-- Every actual integrable real `L²` input has a genuine capped signed decomposition,
actual measurable support control, and true Poisson equations for the removed data. -/
theorem exists_signed_poisson_capped_decomposition (hn : 0 < n) (f : L²ℝ)
    (hf : Integrable (f : D → ℝ)) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : L²ℝ) (U : WholeState) (s : Set D),
      MeasurableSet s ∧ ν ∈ normCap volume (κ : ℝ) ∧ Integrable (ν : D → ℝ) ∧
      (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (κ : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (∀ᵐ x, x ∉ s → isotropicDirichletGlobalValue univ U x = 0) ∧
      ∀ g : L²ℝ, isotropicDirichletForm univ U
        (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) g) =
          ⟪f - ν, poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) g⟫ := by
  obtain ⟨ν, U, hν, _, htest, _, hsat⟩ :=
    exists_wholeSpace_signed_poisson_balayage hn f hf κ hκ
  have hm := lintegral_norm_le_input_of_poisson_mass_cap f ν hf κ hν
  exact ⟨ν, U, poissonBalayageActiveSet U, measurableSet_poissonBalayageActiveSet U,
    hν.1, integrable_of_mem_normMassCap hν, hm,
    (cap_measure_poissonBalayageActiveSet U ν κ hsat).trans hm,
    Eventually.of_forall (fun _ hx ↦ poissonGlobalValue_eq_zero_off_activeSet U hx), htest⟩

end PartialBalayage.Linear
