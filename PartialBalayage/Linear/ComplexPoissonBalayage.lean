/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonActiveSet
public import PartialBalayage.Linear.ComplexPoissonSelfEnergy

/-!
# Genuine complex scalar Poisson partial balayage

The true complex finite obstacles and joint weak exhaustion give one complex norm cap.
Their physical Poisson equation identifies the self-energy, forcing cap alignment and
saturation. The same full input norm mass therefore controls the actual active cover.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)
local notation "H01ℝ" => H01 (univ : Set D)

/-- Every true integrable complex `L²` input has a genuine complex capped Poisson
balayage decomposition, with actual physical PDE and the full input norm mass bound. -/
theorem exists_complex_poisson_capped_decomposition (hn : 0 < n) (f : L²)
    (hf : Integrable (f : D → ℂ)) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν u : L²) (s : Set D),
      MeasurableSet s ∧ ν ∈ normCap volume (κ : ℝ) ∧
      Integrable (ν : D → ℂ) ∧ Integrable (u : D → ℂ) ∧ fourierEnergy 1 u ≠ ⊤ ∧
      (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (κ : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (∀ᵐ x, x ∉ s → u x = 0) ∧
      ∀ W : H01ℝ, inner ℂ u (h01PoissonGenerator W) =
        inner ℂ (f - ν) (h01ComplexValueCLM W) := by
  obtain ⟨ν, u, hν, hi, hE, henergy, hPDE⟩ :=
    exists_wholeSpace_complex_poisson_weak_PDE hn f hf κ hκ
  have he := complex_poisson_self_energy_of_h01_equation u (f - ν) hPDE
  rw [inner_sub_left] at he
  have hp : (κ : ℝ) * ∫ x, ‖u x‖ ≤ ⟪ν, u⟫ := by linarith
  have ha := ae_alignment_saturation_of_pairing_ge κ.coe_nonneg ν u hν.1 hi hp
  have hm := lintegral_norm_le_input_of_complex_poisson_mass_cap f ν hf κ hν
  refine ⟨ν, u, complexPoissonActiveSet u, measurableSet_complexPoissonActiveSet u,
    hν.1, integrable_of_mem_normMassCap hν, hi, hE, hm,
    (cap_measure_complexPoissonActiveSet u ν κ ha.2).trans hm, ?_, hPDE⟩
  exact Eventually.of_forall fun _ hx ↦ complexPoissonValue_eq_zero_off_activeSet u hx

end PartialBalayage.Linear.ComplexPoisson
