/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceVectorBalayage
public import PartialBalayage.Linear.WholeSpaceActiveVolume

/-!
# Actual measurable active sets for global vector balayage

The genuine global observation is used to define the active set. Its measurable outer cover
has exactly the same measure and contains every active point. The true Sobolev norm-test
estimate bounds this measure by the input mass divided by the cap. This supplies an actual
measurable set for the final level-set estimate, without a measurability assumption on a
chosen L² representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace ENNReal

namespace PartialBalayage.Linear

variable {d m : ℕ}

/-- The actual measurable cover of the whole-space state's active set. -/
def globalBalayageActiveSet
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  toMeasurable volume {x | globalVectorDirichletObservation U x ≠ 0}

theorem measurableSet_globalBalayageActiveSet
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m) :
    MeasurableSet (globalBalayageActiveSet U) := measurableSet_toMeasurable _ _

/-- Outside the actual measurable cover the genuine vector value vanishes. -/
theorem globalObservation_eq_zero_off_activeSet
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ globalBalayageActiveSet U) :
    globalVectorDirichletObservation U x = 0 := by
  by_contra hn
  exact hx (subset_toMeasurable volume _ hn)

/-- Genuine global PDE and cap alignment bound the actual measurable active cover. -/
theorem cap_measure_globalBalayageActiveSet
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) {κ : ℝ} (hκ : 0 < κ)
    (hf : Integrable (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m)))
    (hν : Integrable (ν : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m)))
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν, W.val 0⟫)
    (halign : ∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 →
      ν x = (κ / ‖globalVectorDirichletObservation U x‖) •
        globalVectorDirichletObservation U x) :
    ENNReal.ofReal κ * volume (globalBalayageActiveSet U) ≤ ∫⁻ x, ‖f x‖ₑ := by
  have hfr : restrictL2CLM univ f =ᵐ[volume] f := by
    simpa only [Measure.restrict_univ] using restrictL2CLM_ae univ f
  have hνr : restrictL2CLM univ ν =ᵐ[volume] ν := by
    simpa only [Measure.restrict_univ] using restrictL2CLM_ae univ ν
  have ha : ∀ᵐ x ∂volume, vectorDirichletObservation univ U x ≠ 0 →
      restrictL2CLM univ ν x = (κ / ‖vectorDirichletObservation univ U x‖) •
        vectorDirichletObservation univ U x := by
    filter_upwards [halign, hνr, globalVectorDirichletObservation_ae U] with x hx hνx hux
    rw [hνx]
    simpa only [hux] using hx
  have hb := wholeSpace_vectorDirichlet_cap_measure_bound U
    (restrictL2CLM univ f) (restrictL2CLM univ ν) hκ (hf.congr hfr.symm)
    (hν.congr hνr.symm) hpde ha
  have hm : {x | globalVectorDirichletObservation U x ≠ 0} =ᵐ[volume]
      {x | vectorDirichletObservation univ U x ≠ 0} := by
    filter_upwards [globalVectorDirichletObservation_ae U] with x hx
    simp only [hx]
  rw [globalBalayageActiveSet, measure_toMeasurable, measure_congr hm]
  exact hb.trans_eq (lintegral_congr_ae (hfr.fun_comp enorm))

end PartialBalayage.Linear
