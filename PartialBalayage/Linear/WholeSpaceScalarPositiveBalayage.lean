/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceWeakPDE
public import PartialBalayage.Linear.ScalarStateExhaustion
public import PartialBalayage.Linear.ExtendedEnergyMassIdentity
public import PartialBalayage.Linear.WeakDirichletComplementarity
public import PartialBalayage.Linear.WholeSpaceDensityMass

/-!
# Actual positive whole-space scalar partial balayage for the Laplacian

Choose the genuine finite positive scalar obstacles on expanding balls and their joint weak limit.
The true PDE and finite energy-mass identities pass along the same cofinal filter. Weak
lower semicontinuity and the cap then recover actual pointwise alignment and saturation.
The actual state and density are nonnegative. The density retains true integrability,
mass contraction, and the sharp L² energy bound.
No decomposition, locality, regularity, or comparison certificate is a hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- Nonnegative scalar input admits actual global Laplace partial balayage with nonnegative
state and density, genuine weak PDE, mass contraction, and cap complementarity. -/
theorem exists_wholeSpace_scalarPositiveBalayage
    (f : Lp (EuclideanSpace ℝ (Fin 1)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin 1)) volume)
    (hfpos : ∀ᵐ x, 0 ≤ f x 0) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : Lp (EuclideanSpace ℝ (Fin 1)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
      (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) 1),
      (∀ᵐ x, 0 ≤ ν x 0) ∧
      (∀ᵐ x, 0 ≤ globalVectorDirichletObservation U x 0) ∧
      ν ∈ normCap volume (κ : ℝ) ∧
      Integrable (ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin 1)) volume ∧
      (∫ x, ‖ν x‖) ≤ ∫ x, ‖f x‖ ∧
      ‖ν‖ ^ (2 : ℕ) ≤ (κ : ℝ) * ∫ x, ‖f x‖ ∧
      Integrable (globalVectorDirichletObservation U : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin 1)) volume ∧
      (∀ j : Fin 1, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        laplaceBilin univ (U j) W =
          ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν,
            (W : H1amb univ) 0⟫) ∧
      (∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 →
        ν x = ((κ : ℝ) / ‖globalVectorDirichletObservation U x‖) •
          globalVectorDirichletObservation U x) ∧
      (∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 → ‖ν x‖ = (κ : ℝ)) := by
  let Ω : ℕ → Set (EuclideanSpace ℝ (Fin (n + 1))) := fun k ↦ ball 0 (k + 1 : ℝ)
  have hΩ : ∀ k, IsOpen (Ω k) := fun _ ↦ isOpen_ball
  have hΩb : ∀ k, Bornology.IsBounded (Ω k) := fun _ ↦ isBounded_ball
  let mass : ℝ≥0 := ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩
  obtain ⟨ν, U, νlimit, Ulimit, l, hdata, _, _, _, _, hνlimit, hνpos, hUpos,
    hlne, hl, hνt, hUt⟩ :=
    exists_scalarPositiveFiniteObstacle_joint_weak_limit
      Ω hΩ hΩb f hf hfpos κ mass hκ le_rfl
  let : l.NeBot := hlne
  have htest := vector_weak_test_equation_of_joint_limit Ω
    (fun k ↦ (hΩ k).measurableSet) ν U f νlimit Ulimit (fun k ↦ (hdata k).2.1)
      (fun _ hK ↦ eventually_compact_subset_expanding_balls hK) hl hνt hUt
  have hint : ∀ᶠ k in l, Integrable (globalVectorDirichletObservation
      (zeroExtendVectorDirichletState (hΩ k).measurableSet (U k)) :
        EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin 1)) volume := by
    apply Eventually.of_forall
    intro k
    have : IsFiniteMeasure (volume.restrict (Ω k)) :=
      isFiniteMeasure_restrict.mpr ((hΩb k).measure_lt_top (μ := volume)).ne
    rw [globalVectorDirichletObservation_zeroExtend]
    exact integrable_zeroExtendL2 (hΩ k).measurableSet _
      ((Lp.memLp (vectorDirichletObservation (Ω k) (U k))).integrable one_le_two)
  have heq : ∀ᶠ k in l,
      vectorDirichletEnergy (zeroExtendVectorDirichletState (hΩ k).measurableSet (U k)) +
        (κ : ℝ) * ∫ x, ‖globalVectorDirichletObservation
          (zeroExtendVectorDirichletState (hΩ k).measurableSet (U k)) x‖ =
          ⟪f, globalVectorDirichletObservation
            (zeroExtendVectorDirichletState (hΩ k).measurableSet (U k))⟫ :=
    Eventually.of_forall (fun k ↦ extended_vectorDirichlet_energy_mass_identity
      (hΩ k).measurableSet (U k) (ν k) f (hdata k).2.1 (hdata k).2.2.1)
  have hκreal : 0 < (κ : ℝ) := by exact_mod_cast hκ
  obtain ⟨hUint, halign, hsat⟩ := global_vectorDirichlet_complementarity_of_weak_limit
    hκreal f νlimit hνlimit.1 hUt hint heq htest
  have hUglobalpos : ∀ᵐ x, 0 ≤ globalVectorDirichletObservation Ulimit x 0 := by
    filter_upwards [hUpos, globalVectorDirichletObservation_ae Ulimit] with x hx heq
    rwa [heq]
  exact ⟨νlimit, Ulimit, hνpos, hUglobalpos, hνlimit.1, integrable_of_mem_normMassCap hνlimit,
    integral_norm_le_of_mem_normMassCap hνlimit, norm_sq_le_of_mem_normMassCap hνlimit,
    hUint, global_vectorDirichletPDE_of_compactTests Ulimit f νlimit htest, halign, hsat⟩

end PartialBalayage.Linear
