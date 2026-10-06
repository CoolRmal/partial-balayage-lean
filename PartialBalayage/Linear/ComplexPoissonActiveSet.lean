/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonWholeSpaceEquation
public import PartialBalayage.Linear.WeakDirichletComplementarity
public import PartialBalayage.Linear.WholeSpaceDensityMass

/-!
# Actual complex active sets and norm-mass control

The complex value has an actual measurable active cover. A single complex norm cap and
its genuine saturation control this cover by the same full input mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace NNReal ENNReal

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)

/-- The genuine measurable active cover of the complex whole-space value. -/
def complexPoissonActiveSet (u : L²) : Set D := toMeasurable volume {x | u x ≠ 0}

theorem measurableSet_complexPoissonActiveSet (u : L²) :
    MeasurableSet (complexPoissonActiveSet u) := measurableSet_toMeasurable _ _

/-- The actual complex value vanishes outside its measurable active cover. -/
theorem complexPoissonValue_eq_zero_off_activeSet (u : L²) {x : D}
    (hx : x ∉ complexPoissonActiveSet u) : u x = 0 := by
  by_contra hn
  exact hx (subset_toMeasurable volume _ hn)

/-- Genuine complex norm saturation controls cap-weighted active volume. -/
theorem cap_measure_complexPoissonActiveSet (u ν : L²) (κ : ℝ≥0)
    (hsat : ∀ᵐ x, u x ≠ 0 → ‖ν x‖ = (κ : ℝ)) :
    (κ : ℝ≥0∞) * volume (complexPoissonActiveSet u) ≤ ∫⁻ x, ‖ν x‖ₑ := by
  let s : Set D := {x | u x ≠ 0}
  have hs : NullMeasurableSet s volume := by
    have hz := (Lp.aestronglyMeasurable u).norm.nullMeasurableSet_eq_fun
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
  simpa only [complexPoissonActiveSet, measure_toMeasurable, s] using hle

/-- The retained genuine complex mass cap gives the full norm mass contraction. -/
theorem lintegral_norm_le_input_of_complex_poisson_mass_cap (f ν : L²)
    (hf : Integrable (f : D → ℂ)) (κ : ℝ≥0)
    (hν : ν ∈ normMassCap volume κ
      ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩) :
    (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_of_mem_normMassCap hν),
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  exact ENNReal.ofReal_le_ofReal (integral_norm_le_of_mem_normMassCap hν)

end PartialBalayage.Linear.ComplexPoisson
