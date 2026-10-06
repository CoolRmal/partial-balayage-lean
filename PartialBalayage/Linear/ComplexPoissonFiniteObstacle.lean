/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonDirichletEnergyMass
public import PartialBalayage.Linear.FiniteDensityExhaustion

/-!
# Genuine finite signed Poisson obstacles with whole-space mass bounds

The true bounded Poisson operator constructs signed capped densities and states on every
measurable finite-volume domain. Actual Kato gives full density mass contraction, and genuine
zero extension retains the cap, mass, and exact fixed-input energy-mass balance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace NNReal ENNReal

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)

/-- Actual finite signed Poisson obstacles retain genuine full mass and exact global balance. -/
theorem exists_poissonDirichlet_signed_mass_obstacle {Ω : Set D}
    (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (f : L²)
    (hf : Integrable (f : D → ℂ)) (κ mass : ℝ≥0)
    (hmass : (∫ x, ‖f x‖) ≤ (mass : ℝ)) :
    ∃ (ν u : Lp ℂ 2 (volume.restrict Ω)),
      ν ∈ normCap (volume.restrict Ω) (κ : ℝ) ∧
      poissonDirichletOperator hΩ ht ε u = restrictL2CLM Ω f - ν ∧
      (∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ν x = ((κ : ℝ) / ‖u x‖) • u x) ∧
      (∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ‖ν x‖ = (κ : ℝ)) ∧
      zeroExtendL2 hΩ ν ∈ normMassCap volume κ mass ∧
      (∫ x, ‖zeroExtendL2 hΩ ν x‖) ≤ ∫ x, ‖f x‖ ∧
      ε * ‖zeroExtendL2 hΩ u‖ ^ 2 +
        poissonQuadraticDefect ht (zeroExtendL2 hΩ u) +
        (κ : ℝ) * ∫ x, ‖zeroExtendL2 hΩ u x‖ = ⟪f, zeroExtendL2 hΩ u⟫ := by
  obtain ⟨ν, u, hcap, heq, ha, hs⟩ :=
    exists_poissonDirichlet_signed_obstacle hΩ ht hε (restrictL2CLM Ω f) κ.coe_nonneg
  have hm := integral_norm_poissonDirichlet_density_le hΩ ht hε.le
    (restrictL2CLM Ω f) ν u heq ha hs
  have hinput := integral_norm_restrictL2CLM_le Ω f hf
  have hνint := integrable_zeroExtendL2 hΩ ν ((Lp.memLp ν).integrable one_le_two)
  have hglobal : (∫ x, ‖zeroExtendL2 hΩ ν x‖) ≤ ∫ x, ‖f x‖ := by
    rw [integral_norm_zeroExtendL2]
    exact hm.trans hinput
  have hmasscap : zeroExtendL2 hΩ ν ∈ normMassCap volume κ mass := by
    refine ⟨mem_normCap_zeroExtendL2 hΩ κ.coe_nonneg hcap, ?_⟩
    rw [← ofReal_integral_norm_eq_lintegral_enorm hνint,
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hglobal.trans hmass)
  exact ⟨ν, u, hcap, heq, ha, hs, hmasscap, hglobal,
    extended_poissonDirichlet_energy_mass_identity hΩ ht f ν u heq ha⟩

end PartialBalayage.Linear.ComplexPoisson
