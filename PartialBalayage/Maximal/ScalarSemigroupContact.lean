/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceScalarPositiveBalayage
public import PartialBalayage.Linear.WholeSpaceDistributionPDE
public import PartialBalayage.Linear.GlobalBalayageActiveSet
public import PartialBalayage.Maximal.SemigroupSobolevSourceBound

/-!
# Actual scalar obstacle contact for the exact semigroup majorants

The genuine whole-space scalar Sobolev value and density coordinates are actual `L²`
classes. Their true weak PDE gives the ordinary distributional Laplacian with forcing
`ν - f`. The established source theorem consequently gives nonnegative majorant pairings
outside the actual measurable active set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball CenteredMaximal.Ball.DirichletSobolev
open PartialBalayage.Linear PartialBalayage.Constants
open scoped RealInnerProductSpace NNReal ENNReal

namespace PartialBalayage

variable {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "ScalarState" => VectorDirichletState (univ : Set X) 1
local notation "VectorL2" => Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure X)

/-- The actual global scalar state value agrees with its Sobolev value coordinate a.e. -/
theorem scalarGlobalStateValue_ae (U : ScalarState) :
    scalarExhaustionStateValueCLM U =ᵐ[volume] fun x ↦ (U 0 : H1amb univ) 0 x := by
  have hobs := vectorDirichletObservation_ae univ U
  simp only [Measure.restrict_univ] at hobs
  filter_upwards [scalarExhaustionStateValueCLM_ae U, hobs] with x hs ho
  exact hs.trans (congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) ho)

/-- The genuine scalar forcing coordinate of the density minus the input. -/
def scalarGlobalForcing (f ν : VectorL2) : Lp ℝ 2 (volume : Measure X) :=
  scalarExhaustionCoordinateCLM ν - scalarExhaustionCoordinateCLM f

theorem scalarGlobalForcing_ae (f ν : VectorL2) :
    scalarGlobalForcing f ν =ᵐ[volume] fun x ↦ ν x 0 - f x 0 := by
  filter_upwards [Lp.coeFn_sub (scalarExhaustionCoordinateCLM ν)
    (scalarExhaustionCoordinateCLM f), scalarExhaustionCoordinateCLM_ae ν,
    scalarExhaustionCoordinateCLM_ae f] with x hs hν hf
  exact hs.trans (congrArg₂ (· - ·) hν hf)

/-- The true global weak PDE yields the actual scalar `L²` distributional Laplacian. -/
theorem scalarGlobalState_distributionalLaplacian (U : ScalarState) (f ν : VectorL2)
    (hpde : ∀ j : Fin 1, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν, W.val 0⟫) :
    HasLocalDistributionalLaplacian d univ
      (scalarExhaustionStateValueCLM U) (scalarGlobalForcing f ν) := by
  have htest : ∀ j : Fin 1, ∀ φ : X → ℝ, ∀ hφ : IsTestFn univ φ,
      laplaceBilin univ (U j) hφ.toH01 =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)
          hφ.testCls := by
    intro j φ hφ
    simpa only [IsTestFn.toH01_value] using hpde j hφ.toH01
  have hraw := vector_hasLocalDistributionalLaplacian_of_test_equation U f ν htest 0
  intro φ hs hc hu
  calc
    (∫ x, φ x * scalarGlobalForcing f ν x) =
        ∫ x, φ x * (univVectorCoordinateCLM 0 ν x - univVectorCoordinateCLM 0 f x) := by
      apply integral_congr_ae
      filter_upwards [scalarGlobalForcing_ae f ν, univVectorCoordinateCLM_ae 0 ν,
        univVectorCoordinateCLM_ae 0 f] with x hg hν hf
      rw [hg, hν, hf]
    _ = ∫ x, (U 0 : H1amb univ) 0 x * Laplacian.laplacian φ x := hraw φ hs hc hu
    _ = ∫ x, scalarExhaustionStateValueCLM U x * Laplacian.laplacian φ x := by
      apply integral_congr_ae
      filter_upwards [scalarGlobalStateValue_ae U] with x hx
      rw [hx]

/-- Actual heat majorant pairings are integrable and nonnegative off the genuine active set. -/
theorem heatKernelMajorant_pairing_nonneg_off_activeSet (hn : 1 ≤ d)
    (U : ScalarState) (f ν : VectorL2)
    (hu0 : ∀ᵐ x, 0 ≤ globalVectorDirichletObservation U x 0)
    (hpde : ∀ j : Fin 1, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν, W.val 0⟫)
    {a t : ℝ} (hroot : IsHeatTangencyParameter d a) (ht : 0 < t) :
    ∀ᵐ x, Integrable (fun y ↦ heatKernelMajorant d a t (y - x) * (ν y 0 - f y 0)) ∧
      (x ∉ globalBalayageActiveSet U →
        0 ≤ ∫ y, heatKernelMajorant d a t (y - x) * (ν y 0 - f y 0)) := by
  have hupos : ∀ᵐ x, 0 ≤ scalarExhaustionStateValueCLM U x := by
    filter_upwards [hu0,
      scalarExhaustionCoordinateCLM_ae (globalVectorDirichletObservation U)] with x hx hs
    change 0 ≤ scalarExhaustionCoordinateCLM (globalVectorDirichletObservation U) x
    rwa [hs]
  have hcontact := heatKernelMajorant_pairing_nonneg_on_L2_contact d hn hroot ht
    (scalarExhaustionStateValueCLM U) (scalarGlobalForcing f ν) hupos
      (scalarGlobalState_distributionalLaplacian U f ν hpde)
  filter_upwards [hcontact,
    scalarExhaustionCoordinateCLM_ae (globalVectorDirichletObservation U)] with x hx hs
  have hpair :
      (fun y ↦ heatKernelMajorant d a t (y - x) * scalarGlobalForcing f ν y) =ᵐ[volume]
      (fun y ↦ heatKernelMajorant d a t (y - x) * (ν y 0 - f y 0)) := by
    filter_upwards [scalarGlobalForcing_ae f ν] with y hy
    rw [hy]
  refine ⟨hx.1.congr hpair, fun hzero ↦ ?_⟩
  rw [← integral_congr_ae hpair]
  apply hx.2
  change scalarExhaustionCoordinateCLM (globalVectorDirichletObservation U) x = 0
  rw [hs, globalObservation_eq_zero_off_activeSet U hzero, PiLp.zero_apply]

/-- Actual Poisson majorant pairings are integrable and nonnegative off the genuine active set. -/
theorem poissonKernelMajorant_pairing_nonneg_off_activeSet (hn : 1 ≤ d)
    (U : ScalarState) (f ν : VectorL2)
    (hu0 : ∀ᵐ x, 0 ≤ globalVectorDirichletObservation U x 0)
    (hpde : ∀ j : Fin 1, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν, W.val 0⟫)
    {a t : ℝ} (hroot : IsPoissonTangencyParameter d a) (ht : 0 < t) :
    ∀ᵐ x, Integrable (fun y ↦ poissonKernelMajorant d a t (y - x) * (ν y 0 - f y 0)) ∧
      (x ∉ globalBalayageActiveSet U →
        0 ≤ ∫ y, poissonKernelMajorant d a t (y - x) * (ν y 0 - f y 0)) := by
  have hupos : ∀ᵐ x, 0 ≤ scalarExhaustionStateValueCLM U x := by
    filter_upwards [hu0,
      scalarExhaustionCoordinateCLM_ae (globalVectorDirichletObservation U)] with x hx hs
    change 0 ≤ scalarExhaustionCoordinateCLM (globalVectorDirichletObservation U) x
    rwa [hs]
  have hcontact := poissonKernelMajorant_pairing_nonneg_on_L2_contact d hn hroot ht
    (scalarExhaustionStateValueCLM U) (scalarGlobalForcing f ν) hupos
      (scalarGlobalState_distributionalLaplacian U f ν hpde)
  filter_upwards [hcontact,
    scalarExhaustionCoordinateCLM_ae (globalVectorDirichletObservation U)] with x hx hs
  have hpair :
      (fun y ↦ poissonKernelMajorant d a t (y - x) * scalarGlobalForcing f ν y) =ᵐ[volume]
      (fun y ↦ poissonKernelMajorant d a t (y - x) * (ν y 0 - f y 0)) := by
    filter_upwards [scalarGlobalForcing_ae f ν] with y hy
    rw [hy]
  refine ⟨hx.1.congr hpair, fun hzero ↦ ?_⟩
  rw [← integral_congr_ae hpair]
  apply hx.2
  change scalarExhaustionCoordinateCLM (globalVectorDirichletObservation U) x = 0
  rw [hs, globalObservation_eq_zero_off_activeSet U hzero, PiLp.zero_apply]

end PartialBalayage
