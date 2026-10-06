/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonDefectWeakLimit
public import PartialBalayage.Linear.PoissonHeightMonotonicity
public import PartialBalayage.Linear.IsotropicDirichletCoercivity

/-!
# Genuine half-order energy from ordinary weak Poisson-obstacle limits

At each fixed height, the actual quotient energy is bounded by every smaller-height energy.
Weak lower semicontinuity passes the same exact obstacle balances to the ordinary `L²` weak
limit. The genuine spectral zero-height limit then gives finite isotropic half-order energy,
full state integrability, and the actual real energy-mass inequality for a complex value.
The half-order energy finiteness is proved from the genuine zero-height spectral limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)

/-- The same actual approximate balances control every fixed-height limit functional. -/
theorem poissonDefectEnergyMass_le_of_weak_balances {ι : Type*} {l : Filter ι} [l.NeBot]
    {t ε : ι → ℝ} (ht : ∀ k, 0 < t k) {κ : ℝ} (hκ : 0 ≤ κ)
    {u : ι → L²} {limit : L²}
    (hut : Tendsto (fun k ↦ toWeakSpace ℝ L² (u k)) l (𝓝 (toWeakSpace ℝ L² limit)))
    (hheight : Tendsto t l (𝓝 0)) (ℓ : L² →L[ℝ] ℝ)
    (hε : ∀ᶠ k in l, 0 ≤ ε k) (hi : ∀ᶠ k in l, Integrable (u k : D → ℂ))
    (heq : ∀ᶠ k in l, ε k * ‖u k‖ ^ 2 + poissonRealQuadraticDefect (ht k) (u k) +
      κ * ∫ x, ‖u k x‖ = ℓ (u k)) {τ : ℝ} (hτ : 0 < τ) :
    poissonDefectEnergyMass hτ κ limit ≤ ENNReal.ofReal (ℓ limit) := by
  apply poissonDefectEnergyMass_le_of_weak_tendsto hτ κ hut ℓ
  filter_upwards [hheight.eventually (eventually_le_nhds hτ), hε, hi, heq]
    with k hk hεk hik heqk
  rw [poissonDefectEnergyMass_of_integrable hτ hκ (u k) hik]
  apply ENNReal.ofReal_le_ofReal
  have hQ := poissonQuadraticDefect_antitone_height (ht k) hτ hk
    (u k)
  rw [← poissonRealQuadraticDefect_eq, ← poissonRealQuadraticDefect_eq] at hQ
  linarith [mul_nonneg hεk (sq_nonneg ‖u k‖)]

/-- Actual zero-height spectral convergence passes the full extended energy-mass bound. -/
theorem poisson_halfEnergy_mass_le_of_fixed_defects (κ : ℝ) (u : L²) (b : ℝ)
    (hb : ∀ τ : ℝ, ∀ hτ : 0 < τ, poissonDefectEnergyMass hτ κ u ≤ ENNReal.ofReal b) :
    ENNReal.ofReal (2 * Real.pi) * fourierEnergy 1 u +
      ENNReal.ofReal κ * (∫⁻ x, ‖u x‖ₑ) ≤ ENNReal.ofReal b := by
  have hlim := (tendsto_poissonQuadraticSpectral u).add
    (tendsto_const_nhds (x := ENNReal.ofReal κ * (∫⁻ x, ‖u x‖ₑ)))
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  change 0 < τ at hτ
  rw [poissonQuadraticSpectral_eq_ofReal hτ, ← poissonRealQuadraticDefect_eq]
  exact hb τ hτ

/-- The actual weak limit has genuine finite half-order energy and the real mass inequality. -/
theorem poisson_halfEnergy_mass_le_of_weak_balances
    {ι : Type*} {l : Filter ι} [l.NeBot] {t ε : ι → ℝ} (ht : ∀ k, 0 < t k)
    {κ : ℝ} (hκ : 0 < κ) {u : ι → L²} {limit : L²}
    (hut : Tendsto (fun k ↦ toWeakSpace ℝ L² (u k)) l (𝓝 (toWeakSpace ℝ L² limit)))
    (hheight : Tendsto t l (𝓝 0)) (ℓ : L² →L[ℝ] ℝ)
    (hε : ∀ᶠ k in l, 0 ≤ ε k) (hi : ∀ᶠ k in l, Integrable (u k : D → ℂ))
    (heq : ∀ᶠ k in l, ε k * ‖u k‖ ^ 2 + poissonRealQuadraticDefect (ht k) (u k) +
      κ * ∫ x, ‖u k x‖ = ℓ (u k)) :
    Integrable (limit : D → ℂ) ∧
      fourierEnergy 1 limit ≠ ⊤ ∧
      2 * Real.pi * (fourierEnergy 1 limit).toReal +
        κ * ∫ x, ‖limit x‖ ≤ ℓ limit := by
  have hb (τ : ℝ) (hτ : 0 < τ) :=
    poissonDefectEnergyMass_le_of_weak_balances ht hκ.le hut hheight ℓ hε hi heq hτ
  have hlim := poisson_halfEnergy_mass_le_of_fixed_defects κ limit (ℓ limit) hb
  have hint := integrable_poissonState_of_defectEnergyMass_le zero_lt_one hκ limit
    (hb 1 zero_lt_one)
  have hE : fourierEnergy 1 limit ≠ ⊤ := by
    intro htop
    have hc : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by positivity
    have hmul := ENNReal.mul_eq_top.mpr (Or.inl ⟨hc, htop⟩)
    have he := (le_add_of_nonneg_right (show 0 ≤
      ENNReal.ofReal κ * (∫⁻ x, ‖limit x‖ₑ) from zero_le)).trans hlim
    exact ENNReal.ofReal_ne_top (top_unique (hmul ▸ he))
  have hpair : Tendsto (fun k ↦ ℓ (u k)) l (𝓝 (ℓ limit)) :=
    (ℓ.continuous_comp_toWeakSpace_symm.tendsto _).comp hut
  have hp : 0 ≤ ℓ limit := by
    apply ge_of_tendsto hpair
    filter_upwards [hε, heq] with k hk hkeq
    rw [← hkeq]
    exact add_nonneg (add_nonneg (mul_nonneg hk (sq_nonneg _))
      (poissonRealQuadraticDefect_nonneg (ht k) _))
      (mul_nonneg hκ.le (integral_nonneg (fun _ ↦ norm_nonneg _)))
  refine ⟨hint, hE, ?_⟩
  rw [← ENNReal.ofReal_toReal hE, ← ofReal_integral_norm_eq_lintegral_enorm hint,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi),
    ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_add
      (by positivity : 0 ≤ 2 * Real.pi *
        (fourierEnergy 1 limit).toReal)
      (mul_nonneg hκ.le (integral_nonneg (fun _ ↦ norm_nonneg _)))] at hlim
  exact (ENNReal.ofReal_le_ofReal_iff hp).mp hlim

end PartialBalayage.Linear.ComplexPoisson
