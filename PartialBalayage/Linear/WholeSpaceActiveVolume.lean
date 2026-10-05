/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorActiveMass
public import PartialBalayage.Linear.VectorBalayageFinite

/-!
# Actual whole-space active-volume estimates

Positive cap alignment and an integrable density force the active set to have finite
measure even on an infinite ambient measure space. Genuine regularized Sobolev tests
then bound its cap-weighted volume by input mass. The whole-space endpoints use the
actual vector zero-boundary Sobolev graph, its actual coordinatewise weak equation,
and its actual observation. No finite ambient measure or active-volume bound is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

section GeneralMeasure

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure X}

/-- Positive norm pairing with an integrable density forces finite active measure. -/
theorem measure_active_lt_top_of_integrable_density {u ν : X → E} {κ : ℝ}
    (hκ : 0 < κ) (hu : AEStronglyMeasurable u μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖) :
    μ {x | u x ≠ 0} < ⊤ := by
  have hs : NullMeasurableSet {x | u x ≠ 0} μ := by
    have hz := hu.norm.nullMeasurableSet_eq_fun
      (aestronglyMeasurable_const (b := (0 : ℝ)))
    simpa only [norm_eq_zero, Set.compl_ofPred] using hz.compl
  have hint : IntegrableOn (fun _ : X ↦ κ) {x | u x ≠ 0} μ := by
    apply hν.norm.integrableOn.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_of_ae hpair, ae_restrict_mem₀ hs] with x hx ha
    have hnorm : 0 < ‖u x‖ := norm_pos_iff.mpr ha
    have hinner := real_inner_le_norm (u x) (ν x)
    rw [hx] at hinner
    rw [Real.norm_eq_abs, abs_of_pos hκ]
    exact (mul_le_mul_iff_of_pos_right hnorm).mp (by
      simpa only [mul_comm] using hinner)
  exact ((integrableOn_const_iff).mp hint).resolve_left (enorm_ne_zero.mpr hκ.ne')

/-- The regularized-test estimate remains a genuine volume estimate on an infinite measure
space because finite active measure is proved from the density. -/
theorem measure_active_finite_and_cap_mul_volume_le_of_regularized_tests
    {u f ν : X → E} {κ : ℝ} (hκ : 0 < κ)
    (hu : AEStronglyMeasurable u μ) (hf : Integrable f μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖)
    (htest : ∀ k : ℕ, 0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection (1 / (k + 1 : ℝ)) (u x)⟫ ∂μ) :
    μ {x | u x ≠ 0} < ⊤ ∧
      κ * (μ {x | u x ≠ 0}).toReal ≤ ∫ x, ‖f x‖ ∂μ := by
  classical
  have hfinite := measure_active_lt_top_of_integrable_density hκ hu hν hpair
  have hs : NullMeasurableSet {x | u x ≠ 0} μ := by
    have hz := hu.norm.nullMeasurableSet_eq_fun
      (aestronglyMeasurable_const (b := (0 : ℝ)))
    simpa only [norm_eq_zero, Set.compl_ofPred] using hz.compl
  have h := active_mass_le_of_regularized_tests hu hf hν hpair htest
  have heq : (fun x ↦ if u x ≠ 0 then κ else 0) =
      {x | u x ≠ 0}.indicator (fun _ ↦ κ) := by
    funext x
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator₀ hs, integral_const] at h
  exact ⟨hfinite, by
    simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using h⟩

/-- The same true volume estimate in extended nonnegative reals retains finiteness explicitly. -/
theorem cap_mul_measure_active_le_of_regularized_tests_integrable
    {u f ν : X → E} {κ : ℝ} (hκ : 0 < κ)
    (hu : AEStronglyMeasurable u μ) (hf : Integrable f μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖)
    (htest : ∀ k : ℕ, 0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection (1 / (k + 1 : ℝ)) (u x)⟫ ∂μ) :
    ENNReal.ofReal κ * μ {x | u x ≠ 0} ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  obtain ⟨hfinite, hbound⟩ :=
    measure_active_finite_and_cap_mul_volume_le_of_regularized_tests hκ hu hf hν hpair htest
  calc
    ENNReal.ofReal κ * μ {x | u x ≠ 0} =
        ENNReal.ofReal (κ * (μ {x | u x ≠ 0}).toReal) := by
      rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_toReal hfinite.ne]
    _ ≤ ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := ofReal_integral_norm_eq_lintegral_enorm hf

end GeneralMeasure

section ActualEquation

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Actual Sobolev norm-test graphs give the finite active-volume estimate without finite
ambient measure, provided the actual source and density are integrable. -/
theorem measure_active_finite_and_cap_mul_volume_le_of_vector_weak_equation
    (U : Fin m → H01 Ω) (f ν : Fin m → L2D Ω) {κ : ℝ} (hκ : 0 < κ)
    (hf : Integrable (l2VectorValue f) (volume.restrict Ω))
    (hν : Integrable (l2VectorValue ν) (volume.restrict Ω))
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, W.val 0⟫)
    (hpair : ∀ᵐ x ∂(volume.restrict Ω),
      ⟪sobolevVectorValue U x, l2VectorValue ν x⟫ = κ * ‖sobolevVectorValue U x‖) :
    (volume.restrict Ω) {x | sobolevVectorValue U x ≠ 0} < ⊤ ∧
      κ * ((volume.restrict Ω) {x | sobolevVectorValue U x ≠ 0}).toReal ≤
        ∫ x, ‖l2VectorValue f x‖ ∂(volume.restrict Ω) := by
  apply measure_active_finite_and_cap_mul_volume_le_of_regularized_tests hκ
    (memLp_l2VectorValue (fun j ↦ (U j).val 0)).aestronglyMeasurable hf hν hpair
  intro k
  obtain ⟨V, hV⟩ := exists_regularizedDirectionGraph (by positivity : 0 < 1 / (k + 1 : ℝ)) U
  exact regularized_residual_pairing_nonneg_of_weak_equation (by positivity) U V f ν hpde hV

/-- Actual vector observations satisfy the active-volume estimate on any domain, with no
finite-measure instance. Source and density integrability are actual function properties. -/
theorem measure_observation_active_finite_and_cap_mul_volume_le_of_vectorDirichlet
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : VectorDirichletState Ω m)
    (f ν : VectorDirichletL2 Ω m) {κ : ℝ} (hκ : 0 < κ)
    (hf : Integrable f (volume.restrict Ω)) (hν : Integrable ν (volume.restrict Ω))
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x) :
    (volume.restrict Ω) {x | vectorDirichletObservation Ω U x ≠ 0} < ⊤ ∧
      κ * ((volume.restrict Ω) {x | vectorDirichletObservation Ω U x ≠ 0}).toReal ≤
        ∫ x, ‖f x‖ ∂(volume.restrict Ω) := by
  have hfvec := hf.congr (l2VectorValue_vectorDirichletCoordinate_ae Ω f).symm
  have hνvec := hν.congr (l2VectorValue_vectorDirichletCoordinate_ae Ω ν).symm
  obtain ⟨hfinite, hbound⟩ :=
    measure_active_finite_and_cap_mul_volume_le_of_vector_weak_equation (fun j ↦ U j)
      (fun j ↦ vectorDirichletCoordinate Ω j f) (fun j ↦ vectorDirichletCoordinate Ω j ν)
      hκ hfvec hνvec hpde (vectorDirichlet_pairing_of_alignment Ω U ν halign)
  have hs : {x | vectorDirichletObservation Ω U x ≠ 0} =ᵐ[volume.restrict Ω]
      {x | sobolevVectorValue (fun j ↦ U j) x ≠ 0} := by
    filter_upwards [vectorDirichletObservation_ae Ω U] with x hx
    change vectorDirichletObservation Ω U x = sobolevVectorValue (fun j ↦ U j) x at hx
    change (vectorDirichletObservation Ω U x ≠ 0) =
      (sobolevVectorValue (fun j ↦ U j) x ≠ 0)
    rw [hx]
  rw [measure_congr hs]
  exact ⟨hfinite, hbound.trans_eq (integral_congr_ae
    ((l2VectorValue_vectorDirichletCoordinate_ae Ω f).fun_comp norm))⟩

end ActualEquation

section WholeSpace

variable {d m : ℕ}

/-- Genuine whole-space vector states with actual weak PDE and cap alignment have finite
active volume bounded by input mass. The ambient Euclidean measure is unrestricted. -/
theorem wholeSpace_vectorDirichlet_active_volume_bound
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : VectorDirichletL2 (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    {κ : ℝ} (hκ : 0 < κ) (hf : Integrable f) (hν : Integrable ν)
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        ⟪vectorDirichletCoordinate univ j f - vectorDirichletCoordinate univ j ν, W.val 0⟫)
    (halign : ∀ᵐ x, vectorDirichletObservation univ U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation univ U x‖) •
        vectorDirichletObservation univ U x) :
    volume {x | vectorDirichletObservation univ U x ≠ 0} < ⊤ ∧
      κ * (volume {x | vectorDirichletObservation univ U x ≠ 0}).toReal ≤
        ∫ x, ‖f x‖ := by
  have h := measure_observation_active_finite_and_cap_mul_volume_le_of_vectorDirichlet
    univ U f ν hκ (by simpa only [Measure.restrict_univ] using hf)
    (by simpa only [Measure.restrict_univ] using hν) hpde
    (by simpa only [Measure.restrict_univ] using halign)
  simpa only [Measure.restrict_univ] using h

/-- The genuine whole-space vector active-volume estimate in the extended-real form used
by weak-type bounds. -/
theorem wholeSpace_vectorDirichlet_cap_measure_bound
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : VectorDirichletL2 (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    {κ : ℝ} (hκ : 0 < κ) (hf : Integrable f) (hν : Integrable ν)
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        ⟪vectorDirichletCoordinate univ j f - vectorDirichletCoordinate univ j ν, W.val 0⟫)
    (halign : ∀ᵐ x, vectorDirichletObservation univ U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation univ U x‖) •
        vectorDirichletObservation univ U x) :
    ENNReal.ofReal κ * volume {x | vectorDirichletObservation univ U x ≠ 0} ≤
      ∫⁻ x, ‖f x‖ₑ := by
  obtain ⟨hfinite, hbound⟩ := wholeSpace_vectorDirichlet_active_volume_bound U f ν hκ hf hν
    hpde halign
  calc
    ENNReal.ofReal κ * volume {x | vectorDirichletObservation univ U x ≠ 0} =
        ENNReal.ofReal (κ *
          (volume {x | vectorDirichletObservation univ U x ≠ 0}).toReal) := by
      rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_toReal hfinite.ne]
    _ ≤ ENNReal.ofReal (∫ x, ‖f x‖) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := ofReal_integral_norm_eq_lintegral_enorm hf

/-- The scalar positive set inherits the true whole-space active-volume estimate. This
specialization can be used directly with nonnegative scalar states in the semigroup argument. -/
theorem wholeSpace_scalarDirichlet_positive_volume_bound
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) 1)
    (f ν : VectorDirichletL2 (univ : Set (EuclideanSpace ℝ (Fin d))) 1)
    {κ : ℝ} (hκ : 0 < κ) (hf : Integrable f) (hν : Integrable ν)
    (hpde : ∀ j : Fin 1, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        ⟪vectorDirichletCoordinate univ j f - vectorDirichletCoordinate univ j ν, W.val 0⟫)
    (halign : ∀ᵐ x, vectorDirichletObservation univ U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation univ U x‖) •
        vectorDirichletObservation univ U x) :
    volume {x | 0 < vectorDirichletObservation univ U x 0} < ⊤ ∧
      κ * (volume {x | 0 < vectorDirichletObservation univ U x 0}).toReal ≤
        ∫ x, ‖f x‖ := by
  obtain ⟨hfinite, hbound⟩ := wholeSpace_vectorDirichlet_active_volume_bound U f ν hκ hf hν
    hpde halign
  have hsub : {x | 0 < vectorDirichletObservation univ U x 0} ⊆
      {x | vectorDirichletObservation univ U x ≠ 0} := by
    intro x hx hz
    change 0 < vectorDirichletObservation univ U x 0 at hx
    have hz0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) hz
    simp only [PiLp.zero_apply] at hz0
    exact (ne_of_gt hx) hz0
  exact ⟨(measure_mono hsub).trans_lt hfinite,
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite.ne (measure_mono hsub))
      hκ.le).trans hbound⟩

end WholeSpace

end PartialBalayage.Linear
