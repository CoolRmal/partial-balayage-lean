/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonFiniteObstacle
public import PartialBalayage.Linear.ComplexPoissonFiniteUniformBounds
public import PartialBalayage.Linear.ComplexPoissonHalfEnergyLimit
public import PartialBalayage.Linear.JointWeakCompactness
public import PartialBalayage.Linear.PoissonStateExhaustion

/-!
# Actual joint weak exhaustion of finite signed Poisson obstacles

Positive Poisson heights are chosen genuinely small enough for the fixed input's spectral
bound, then decrease to zero. The true finite obstacles have uniform ordinary `L²` states
and capped finite-mass densities. Actual joint weak compactness and the same energy-mass
identities produce a genuine half-energy limit without a compactness or regularity certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)

/-- The actual finite family has a genuine ordinary joint weak limit
with proved half-order energy. -/
theorem exists_poissonFinite_joint_weak_limit (hn : 0 < n)
    (Ω : ℕ → Set D) (hΩ : ∀ k, MeasurableSet (Ω k))
    (hfin : ∀ k, volume (Ω k) ≠ ⊤) (f : L²) (hf : Integrable (f : D → ℂ))
    (κ mass : ℝ≥0) (hκ : 0 < κ) (hmass : (∫ x, ‖f x‖) ≤ (mass : ℝ)) :
    ∃ (t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
      (ν u : ∀ k, Lp ℂ 2 (volume.restrict (Ω k))) (νlimit limit : L²) (l : Filter ℕ),
      Tendsto t atTop (𝓝 0) ∧
      (∀ k, poissonDirichletOperator (hΩ k) (ht k) (t k) (u k) =
        restrictL2CLM (Ω k) f - ν k) ∧
      (∀ k, zeroExtendL2 (hΩ k) (ν k) ∈ normMassCap volume κ mass) ∧
      νlimit ∈ normMassCap volume κ mass ∧ l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ L² (zeroExtendL2 (hΩ k) (ν k))) l
        (𝓝 (toWeakSpace ℝ L² νlimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ L² (zeroExtendL2 (hΩ k) (u k))) l
        (𝓝 (toWeakSpace ℝ L² limit)) ∧
      (∃ B : ℝ, ∀ k, ‖zeroExtendL2 (hΩ k) (u k)‖ ≤ B) ∧
      Integrable (limit : D → ℂ) ∧ fourierEnergy 1 limit ≠ ⊤ ∧
      2 * Real.pi * (fourierEnergy 1 limit).toReal +
        (κ : ℝ) * ∫ x, ‖limit x‖ ≤ ⟪f, limit⟫ := by
  have hκreal : 0 < (κ : ℝ) := by exact_mod_cast hκ
  obtain ⟨R, C, hR, hC, hbound⟩ := exists_poisson_balance_uniform_bounds hn f hκreal
  obtain ⟨t, ht, htz, hrate⟩ := exists_uniform_poisson_heights hR
  have hex (k : ℕ) := by
    let : IsFiniteMeasure (volume.restrict (Ω k)) := isFiniteMeasure_restrict.mpr (hfin k)
    exact exists_poissonDirichlet_signed_mass_obstacle (hΩ k) (ht k) (ht k) f hf κ mass hmass
  choose ν u hcap heq ha hs hmasscap hmassglobal hbalance using hex
  have hi (k : ℕ) : Integrable (zeroExtendL2 (hΩ k) (u k) : D → ℂ) := by
    let : IsFiniteMeasure (volume.restrict (Ω k)) := isFiniteMeasure_restrict.mpr (hfin k)
    exact integrable_zeroExtendL2 (hΩ k) (u k) ((Lp.memLp (u k)).integrable one_le_two)
  have hu (k : ℕ) : ‖zeroExtendL2 (hΩ k) (u k)‖ ≤ C + 1 := by
    have hb : poissonQuadraticDefect (ht k)
        (zeroExtendL2 (hΩ k) (u k)) +
        (κ : ℝ) * ∫ x, ‖zeroExtendL2 (hΩ k) (u k) x‖ ≤ ⟪f, zeroExtendL2 (hΩ k) (u k)⟫ := by
      linarith [hbalance k, mul_nonneg (ht k).le (sq_nonneg ‖zeroExtendL2 (hΩ k) (u k)‖)]
    have hN := (hbound (ht k) (hrate k) _ (hi k) hb).2.2
    nlinarith [sq_nonneg (‖zeroExtendL2 (hΩ k) (u k)‖ - 1)]
  obtain ⟨νlimit, limit, l, hνlimit, _, hlne, hl, hνt, hut⟩ :=
    exists_joint_weak_filter_normMassCap κ mass (C + 1)
      (fun k ↦ zeroExtendL2 (hΩ k) (ν k)) (fun k ↦ zeroExtendL2 (hΩ k) (u k)) hmasscap hu
  let : l.NeBot := hlne
  have he : ∀ᶠ k in l, t k * ‖zeroExtendL2 (hΩ k) (u k)‖ ^ 2 +
      poissonRealQuadraticDefect (ht k) (zeroExtendL2 (hΩ k) (u k)) +
      (κ : ℝ) * ∫ x, ‖zeroExtendL2 (hΩ k) (u k) x‖ =
        (innerSL ℝ f) (zeroExtendL2 (hΩ k) (u k)) := by
    apply Eventually.of_forall
    intro k
    rw [poissonRealQuadraticDefect_eq]
    exact hbalance k
  have hlimit := poisson_halfEnergy_mass_le_of_weak_balances ht hκreal hut
    (htz.mono_left hl) (innerSL ℝ f) (Eventually.of_forall (fun k ↦ (ht k).le))
      (Eventually.of_forall hi) he
  exact ⟨t, ht, ν, u, νlimit, limit, l, htz, heq, hmasscap, hνlimit, hlne, hl, hνt, hut,
    ⟨C + 1, hu⟩, hlimit.1, hlimit.2.1, hlimit.2.2⟩

end PartialBalayage.Linear.ComplexPoisson
