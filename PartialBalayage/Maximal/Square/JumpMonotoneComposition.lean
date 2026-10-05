/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpBallObstacle
public import PartialBalayage.Linear.VectorSobolevComposition
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Genuine monotone tests in the stable jump energy space

Every Lipschitz scalar function vanishing at zero defines an actual composition of
the full singular jump graph and preserves the zero-exterior condition. Monotonicity
makes its mixed jump energy nonnegative. In particular the actual regularized sign
is an admissible positive test; no chain rule or test-admissibility premise is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open PartialBalayage.Linear
open scoped NNReal RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Lipschitz composition preserves actual square integrability of every singular increment. -/
theorem memLp_coordinateJump_of_lipschitz (α : ℝ) (η : ℝ → ℝ) {K : ℝ≥0}
    (hη : LipschitzWith K η) (hη0 : η 0 = 0) (U : StableJumpEnergySpace α) (i : Fin 2) :
    MemLp (coordinateJump (hη.compLp hη0 (stableJumpValue α U) : E → ℝ) i) 2
      (spatialJumpMeasure α) := by
  let u := hη.compLp hη0 (stableJumpValue α U)
  have hu := Lp.aestronglyMeasurable u
  have hm : AEStronglyMeasurable (coordinateJump (u : E → ℝ) i)
      (spatialJumpMeasure α) :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_coordinateJumpPoint α i)).sub
      (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_fst
        (μ := (volume : Measure E)) (ν := stableJumpMeasure α)))
  apply ((Lp.memLp (stableJumpData α U i)).norm.const_mul (K : ℝ)).mono' hm
  have he := hη.coeFn_compLp hη0 (stableJumpValue α U)
  filter_upwards [stableJumpData_ae α U i,
    (quasiMeasurePreserving_coordinateJumpPoint α i).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae he] with p hU hx hy
  change ‖u (coordinateJumpPoint i p) - u p.1‖ ≤ K * ‖stableJumpData α U i p‖
  rw [hx, hy, hU]
  simpa only [Function.comp_apply, coordinateJump] using
    hη.norm_sub_le (stableJumpValue α U (coordinateJumpPoint i p)) (stableJumpValue α U p.1)

/-- The actual Lipschitz composition in the full singular energy graph. -/
def stableJumpLipschitzComposition (α : ℝ) (η : ℝ → ℝ) {K : ℝ≥0}
    (hη : LipschitzWith K η) (hη0 : η 0 = 0) (U : StableJumpEnergySpace α) :
    StableJumpEnergySpace α := by
  refine ⟨WithLp.toLp 2 (hη.compLp hη0 (stableJumpValue α U),
    WithLp.toLp 2 fun i ↦ (memLp_coordinateJump_of_lipschitz α η hη hη0 U i).toLp
      (coordinateJump (hη.compLp hη0 (stableJumpValue α U) : E → ℝ) i)), ?_⟩
  change ∀ i : Fin 2, _
  exact fun i ↦ (memLp_coordinateJump_of_lipschitz α η hη hη0 U i).coeFn_toLp

theorem stableJumpLipschitzComposition_value (α : ℝ) (η : ℝ → ℝ) {K : ℝ≥0}
    (hη : LipschitzWith K η) (hη0 : η 0 = 0) (U : StableJumpEnergySpace α) :
    stableJumpValue α (stableJumpLipschitzComposition α η hη hη0 U) =
      hη.compLp hη0 (stableJumpValue α U) := rfl

/-- Lipschitz composition preserves the actual zero-exterior condition. -/
theorem stableJumpLipschitzComposition_mem_supported (α : ℝ) {S : Set E}
    (hS : MeasurableSet S) (η : ℝ → ℝ) {K : ℝ≥0}
    (hη : LipschitzWith K η) (hη0 : η 0 = 0) {U : StableJumpEnergySpace α}
    (hU : U ∈ stableJumpSupported α S) :
    stableJumpLipschitzComposition α η hη hη0 U ∈ stableJumpSupported α S := by
  rw [mem_stableJumpSupported_iff α hS] at hU ⊢
  have he := hη.coeFn_compLp hη0 (stableJumpValue α U)
  filter_upwards [hU, he] with x hx he
  intro hxo
  rw [stableJumpLipschitzComposition_value, he, Function.comp_apply, hx hxo, hη0]

/-- The genuine zero-exterior Lipschitz test. -/
def stableJumpDirichletComposition (α : ℝ) {S : Set E} (hS : MeasurableSet S)
    (η : ℝ → ℝ) {K : ℝ≥0} (hη : LipschitzWith K η) (hη0 : η 0 = 0)
    (U : StableJumpDirichletSpace α S) : StableJumpDirichletSpace α S :=
  ⟨stableJumpLipschitzComposition α η hη hη0 U.val,
    stableJumpLipschitzComposition_mem_supported α hS η hη hη0 U.property⟩

private theorem monotone_increment_nonneg {η : ℝ → ℝ} (hη : Monotone η) (a b : ℝ) :
    0 ≤ (a - b) * (η a - η b) := by
  rcases le_total b a with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hη h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (hη h))

/-- A true monotone Lipschitz test has nonnegative mixed singular jump energy. -/
theorem stableJumpForm_lipschitzComposition_nonneg (α : ℝ) (η : ℝ → ℝ) {K : ℝ≥0}
    (hη : LipschitzWith K η) (hη0 : η 0 = 0) (hm : Monotone η)
    (U : StableJumpEnergySpace α) :
    0 ≤ stableJumpForm α U (stableJumpLipschitzComposition α η hη hη0 U) := by
  rw [stableJumpForm, PiLp.inner_apply]
  apply Finset.sum_nonneg
  intro i _
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  have he := hη.coeFn_compLp hη0 (stableJumpValue α U)
  filter_upwards [stableJumpData_ae α U i,
    stableJumpData_ae α (stableJumpLipschitzComposition α η hη hη0 U) i,
    (quasiMeasurePreserving_coordinateJumpPoint α i).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae he] with p hU hV hx hy
  rw [Real.inner_apply, hU, hV, stableJumpLipschitzComposition_value]
  unfold coordinateJump
  rw [hx, hy]
  exact monotone_increment_nonneg hm _ _

/-- The actual regularized scalar sign is monotone. -/
theorem monotone_regularizedDirection_scalar {ε : ℝ} (hε : 0 < ε) :
    Monotone (regularizedDirection («E» := ℝ) ε) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun r ↦ (hasFDerivAt_regularizedDirection hε r).hasDerivAt)
  intro r
  have h := inner_regularizedDirectionDeriv_nonneg hε r (1 : ℝ)
  simpa only [Real.inner_apply, one_mul, Pi.zero_apply] using h

/-- The actual regularized sign is a genuine test in the zero-exterior jump space. -/
def stableJumpDirichletSignTest (α : ℝ) {S : Set E} (hS : MeasurableSet S)
    {ε : ℝ} (hε : 0 < ε) (U : StableJumpDirichletSpace α S) :
    StableJumpDirichletSpace α S :=
  stableJumpDirichletComposition α hS (regularizedDirection ε)
    (lipschitzWith_regularizedDirection hε) (by simp [regularizedDirection]) U

/-- Its actual value is the regularized sign of the genuine restricted state value. -/
theorem stableJumpDirichletSignTest_value_ae (α : ℝ) {S : Set E}
    (hS : MeasurableSet S) {ε : ℝ} (hε : 0 < ε)
    (U : StableJumpDirichletSpace α S) :
    (stableJumpDirichletValue α S (stableJumpDirichletSignTest α hS hε U) : E → ℝ)
      =ᵐ[volume.restrict S]
    fun x ↦ regularizedDirection ε (stableJumpDirichletValue α S U x) := by
  have he := (lipschitzWith_regularizedDirection hε).coeFn_compLp
    (by simp [regularizedDirection]) (stableJumpValue α U.val)
  filter_upwards [restrictL2CLM_ae S (stableJumpDirichletGlobalValue α S U),
    restrictL2CLM_ae S (stableJumpDirichletGlobalValue α S
      (stableJumpDirichletSignTest α hS hε U)), ae_restrict_of_ae he] with x hU hV hx
  exact hV.trans (hx.trans (congrArg (regularizedDirection ε) hU.symm))

/-- The actual stable energy paired against its actual regularized sign is nonnegative. -/
theorem stableJumpForm_signTest_nonneg (α : ℝ) {S : Set E} (hS : MeasurableSet S)
    {ε : ℝ} (hε : 0 < ε) (U : StableJumpDirichletSpace α S) :
    0 ≤ stableJumpForm α U.val (stableJumpDirichletSignTest α hS hε U).val :=
  stableJumpForm_lipschitzComposition_nonneg α (regularizedDirection ε)
    (lipschitzWith_regularizedDirection hε) (by simp [regularizedDirection])
    (monotone_regularizedDirection_scalar hε) U.val

end PartialBalayage.Maximal.Square
