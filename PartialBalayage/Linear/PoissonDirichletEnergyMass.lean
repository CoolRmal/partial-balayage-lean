/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonDirichletMass
public import PartialBalayage.Linear.PoissonQuadraticSpectral

/-!
# Exact energy and mass of genuine finite Poisson obstacles

The actual bounded equation can be tested with its own real `L²` state. Genuine cap
alignment evaluates the density pairing. The resulting identity uses the actual global
Poisson quadratic defect of the zero extension and the fixed global input pairing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℝ 2 (volume : Measure D)

/-- The finite state's actual global Poisson energy, using its genuine zero extension. -/
def poissonDirichletEnergy {Ω : Set D} (hΩ : MeasurableSet Ω) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (volume.restrict Ω)) : ℝ :=
  poissonQuadraticDefect ht (Complex.ofRealCLM.compLp (zeroExtendL2 hΩ u))

/-- The actual global defect equals the finite-domain self-adjoint difference quotient. -/
theorem poissonDirichletEnergy_eq {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 (volume.restrict Ω)) :
    poissonDirichletEnergy hΩ ht u =
      t⁻¹ * (‖u‖ ^ 2 - ⟪poissonDirichletAverage hΩ ht u, u⟫) := by
  rw [poissonDirichletEnergy, poissonQuadraticDefect, poissonQuotientL2_complexify,
    re_inner_complexifyL2, real_inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, norm_zeroExtendL2,
    real_inner_comm (poissonConvolutionL2 ht (zeroExtendL2 hΩ u)) (zeroExtendL2 hΩ u),
    inner_global_zeroExtendL2 hΩ]
  rfl

theorem poissonDirichletEnergy_nonneg {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 (volume.restrict Ω)) :
    0 ≤ poissonDirichletEnergy hΩ ht u := poissonQuadraticDefect_nonneg ht _

/-- Actual pointwise cap alignment evaluates the entire state-density pairing. -/
theorem inner_poissonDirichlet_density_state {Ω : Set D}
    [IsFiniteMeasure (volume.restrict Ω)] (ν u : Lp ℝ 2 (volume.restrict Ω)) {κ : ℝ}
    (ha : ∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ν x = (κ / ‖u x‖) • u x) :
    ⟪ν, u⟫ = κ * ∫ x, ‖u x‖ ∂volume.restrict Ω := by
  rw [real_inner_comm u ν, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  by_cases hu : u x = 0
  · simp only [hu, inner_zero_left, norm_zero, mul_zero]
  · rw [hx hu, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
    field_simp [norm_ne_zero_iff.mpr hu]

/-- Testing the true finite equation at the true state gives its exact energy-mass identity. -/
theorem poissonDirichlet_energy_mass_identity {Ω : Set D} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {t ε κ : ℝ} (ht : 0 < t)
    (f ν u : Lp ℝ 2 (volume.restrict Ω))
    (heq : poissonDirichletOperator hΩ ht ε u = f - ν)
    (ha : ∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ν x = (κ / ‖u x‖) • u x) :
    ε * ‖u‖ ^ 2 + poissonDirichletEnergy hΩ ht u +
      κ * ∫ x, ‖u x‖ ∂volume.restrict Ω = ⟪f, u⟫ := by
  have h := congrArg (fun v : Lp ℝ 2 (volume.restrict Ω) ↦ ⟪v, u⟫) heq
  rw [inner_poissonDirichletOperator, real_inner_self_eq_norm_sq, inner_sub_left,
    inner_poissonDirichlet_density_state ν u ha] at h
  rw [poissonDirichletEnergy_eq]
  linarith

/-- The genuine extended balance pairs all finite states against one fixed global input. -/
theorem extended_poissonDirichlet_energy_mass_identity {Ω : Set D} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {t ε κ : ℝ} (ht : 0 < t)
    (f : L²) (ν u : Lp ℝ 2 (volume.restrict Ω))
    (heq : poissonDirichletOperator hΩ ht ε u = restrictL2CLM Ω f - ν)
    (ha : ∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ν x = (κ / ‖u x‖) • u x) :
    ε * ‖zeroExtendL2 hΩ u‖ ^ 2 +
      poissonQuadraticDefect ht (Complex.ofRealCLM.compLp (zeroExtendL2 hΩ u)) +
      κ * ∫ x, ‖zeroExtendL2 hΩ u x‖ = ⟪f, zeroExtendL2 hΩ u⟫ := by
  rw [norm_zeroExtendL2, integral_norm_zeroExtendL2, inner_global_zeroExtendL2]
  exact poissonDirichlet_energy_mass_identity hΩ ht (restrictL2CLM Ω f) ν u heq ha

end PartialBalayage.Linear
