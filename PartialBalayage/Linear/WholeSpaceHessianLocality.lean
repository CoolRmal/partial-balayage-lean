/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceHessianRegularity
public import PartialBalayage.Linear.SchwartzDirichletTest
public import PartialBalayage.Linear.WholeSpaceVectorBalayage
public import PartialBalayage.Linear.HessianTrace
public import PartialBalayage.Linear.BeurlingHessianIdentity
public import PartialBalayage.Linear.HessianLinearity
public import PartialBalayage.Linear.WholeSpaceActiveVolume

/-!
# Actual Hessian cancellation for constructed vector partial balayage

The genuine whole-space weak equation implies represented L² second derivatives and full
Hessian cancellation on the inactive vector state set. Thus the constructed capped density
and input have identical Hessian action off that set. The existence endpoint has no graph,
regularity, distributional equation, or operator cancellation certificate as a hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace SchwartzMap Laplacian NNReal

namespace PartialBalayage.Linear

variable {d m : ℕ}

/-- Complexification of the actual univ-restricted L² space respects subtraction. -/
theorem complexUnivL2_sub
    (f g : L2D (univ : Set (EuclideanSpace ℝ (Fin d)))) :
    complexUnivL2 (f - g) = complexUnivL2 f - complexUnivL2 g := by
  apply Lp.ext
  have hsub := Lp.coeFn_sub f g
  simp only [Measure.restrict_univ] at hsub
  filter_upwards [complexUnivL2_ae (f - g), complexUnivL2_ae f, complexUnivL2_ae g,
    hsub, Lp.coeFn_sub (complexUnivL2 f) (complexUnivL2 g)] with x hfg hf hg hs ht
  simp only [hfg, hf, hg, hs, ht, Pi.sub_apply, Complex.ofReal_sub]

/-- The genuine global active state set is measurable, using the actual L² representative. -/
theorem measurableSet_globalVectorDirichlet_active
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m) :
    MeasurableSet {x | globalVectorDirichletObservation U x ≠ 0} := by
  have hzero := (Lp.stronglyMeasurable (globalVectorDirichletObservation U)).measurableSet_eq_fun
    (stronglyMeasurable_const (b := (0 : EuclideanSpace ℝ (Fin m))))
  simpa only [Set.compl_ofPred] using hzero.compl

/-- The actual global PDE and cap alignment bound the genuine active set in extended reals. -/
theorem globalVectorDirichlet_cap_measure_bound
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {κ : ℝ} (hκ : 0 < κ) (hf : Integrable f volume) (hν : Integrable ν volume)
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) (W.val 0))
    (halign : ∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 →
      ν x = (κ / ‖globalVectorDirichletObservation U x‖) •
        globalVectorDirichletObservation U x) :
    ENNReal.ofReal κ * volume {x | globalVectorDirichletObservation U x ≠ 0} ≤
      ∫⁻ x, ‖f x‖ₑ := by
  let f' := restrictL2CLM univ f
  let ν' := restrictL2CLM univ ν
  have hf' : f' =ᵐ[volume] f := by
    simpa only [Measure.restrict_univ] using restrictL2CLM_ae univ f
  have hν' : ν' =ᵐ[volume] ν := by
    simpa only [Measure.restrict_univ] using restrictL2CLM_ae univ ν
  have hpde' : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        inner ℝ (vectorDirichletCoordinate univ j f' -
          vectorDirichletCoordinate univ j ν') (W.val 0) := hpde
  have halign' : ∀ᵐ x ∂volume, vectorDirichletObservation univ U x ≠ 0 →
      ν' x = (κ / ‖vectorDirichletObservation univ U x‖) •
        vectorDirichletObservation univ U x := by
    filter_upwards [hν', globalVectorDirichletObservation_ae U, halign] with x hn hu ha
    simpa only [hn, ← hu] using ha
  have hs : {x | globalVectorDirichletObservation U x ≠ 0} =ᵐ[volume]
      {x | vectorDirichletObservation univ U x ≠ 0} := by
    filter_upwards [globalVectorDirichletObservation_ae U] with x hu
    rw [hu]
  rw [measure_congr hs]
  exact (wholeSpace_vectorDirichlet_cap_measure_bound U f' ν' hκ
    (hf.congr hf'.symm) (hν.congr hν'.symm) hpde' halign').trans_eq
      (lintegral_congr_ae (hf'.fun_comp enorm))

/-- The actual global vector observation represents every genuine scalar state value. -/
theorem globalVectorDirichletObservation_values_ae
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m) :
    ∀ᵐ x ∂volume, globalVectorDirichletObservation U x =
      WithLp.toLp 2 (fun j : Fin m ↦ (U j).val 0 x) := by
  have hvalues := vectorDirichletObservation_ae univ U
  simp only [Measure.restrict_univ] at hvalues
  exact (globalVectorDirichletObservation_ae U).trans hvalues

/-- The actual all-H01 PDE gives Hessian cancellation for every residual coordinate
on the vector state's inactive set. All second-gradient graphs are constructed from the PDE. -/
theorem vector_hessianL2_eq_zero_on_inactive_of_weak_equation
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) (W.val 0)) :
    ∀ᵐ x ∂volume, globalVectorDirichletObservation U x = 0 → ∀ j : Fin m,
      hessianL2 (complexUnivL2
        (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)) x = 0 := by
  have hj (j : Fin m) : ∀ᵐ x ∂volume, (U j).val 0 x = 0 →
      hessianL2 (complexUnivL2
        (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)) x = 0 :=
    ae_hessianL2_eq_zero_on_H01_value_zero_of_laplace_equation (U j) _
      (laplacian_complexGlobalGraphCoordinate_of_H01_equation (U j) _ (hpde j))
  filter_upwards [ae_all_iff.mpr hj, globalVectorDirichletObservation_values_ae U]
    with x hh hvalues
  intro hu j
  have hzero : (U j).val 0 x = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v j) (hvalues.symm.trans hu)
    simpa only [PiLp.toLp_apply, PiLp.zero_apply] using h
  exact hh j hzero

/-- The full Hessian of input and capped density agrees off the genuine active vector set. -/
theorem vector_hessianL2_eq_on_inactive_of_weak_equation
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) (W.val 0)) :
    ∀ᵐ x ∂volume, globalVectorDirichletObservation U x = 0 → ∀ j : Fin m,
      hessianL2 (complexUnivL2 (univVectorCoordinateCLM j f)) x =
        hessianL2 (complexUnivL2 (univVectorCoordinateCLM j ν)) x := by
  have hzero := vector_hessianL2_eq_zero_on_inactive_of_weak_equation U f ν hpde
  simp only [complexUnivL2_sub, hessianL2_sub] at hzero
  have hsub (j : Fin m) := Lp.coeFn_sub
    (hessianL2 (complexUnivL2 (univVectorCoordinateCLM j f)))
    (hessianL2 (complexUnivL2 (univVectorCoordinateCLM j ν)))
  filter_upwards [hzero, ae_all_iff.mpr hsub] with x hz hs
  intro hu j
  exact sub_eq_zero.mp (by simpa only [hs j, Pi.sub_apply] using hz hu j)

/-- The actual source residual itself also vanishes on the inactive vector state set,
by genuine second-order locality of the weak Laplace equation. -/
theorem vector_complex_residual_eq_zero_on_inactive_of_weak_equation
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) (W.val 0)) :
    ∀ᵐ x ∂volume, globalVectorDirichletObservation U x = 0 → ∀ j : Fin m,
      complexUnivL2 (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) x = 0 := by
  have hj (j : Fin m) : ∀ᵐ x ∂volume, (U j).val 0 x = 0 →
      complexUnivL2 (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) x = 0 := by
    have hl := ae_forcing_eq_zero_on_value_zero_of_weak_laplacian isOpen_univ (U j)
      (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)
      (fun W ↦ by simpa only [l2Functional_apply] using hpde j W)
    simp only [Measure.restrict_univ] at hl
    filter_upwards [hl, complexUnivL2_ae
      (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)] with x hx hcomplex
    intro hu
    rw [hcomplex, hx hu, Complex.ofReal_zero]
  filter_upwards [ae_all_iff.mpr hj, globalVectorDirichletObservation_values_ae U]
    with x hh hvalues
  intro hu j
  have hzero : (U j).val 0 x = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v j) (hvalues.symm.trans hu)
    simpa only [PiLp.toLp_apply, PiLp.zero_apply] using h
  exact hh j hzero

/-- Actual whole-space densities equal their inputs on the inactive set, by the true PDE. -/
theorem vector_density_eq_input_on_inactive_of_global_weak_equation
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) (W.val 0)) :
    ∀ᵐ x ∂volume, globalVectorDirichletObservation U x = 0 → ν x = f x := by
  have hlocal := ae_vectorDirichlet_density_eq_input_on_inactive isOpen_univ U
    (restrictL2CLM univ f) (restrictL2CLM univ ν) hpde
  have hf := restrictL2CLM_ae univ f
  have hν := restrictL2CLM_ae univ ν
  simp only [Measure.restrict_univ] at hlocal hf hν
  filter_upwards [hlocal, hf, hν, globalVectorDirichletObservation_ae U]
    with x hx hfx hνx hu
  intro hz
  exact hνx.symm.trans ((hx (hu.symm.trans hz)).trans hfx)

/-- The genuine traceless Hessian of every residual coordinate vanishes off the actual active
set as a consequence of the actual vector PDE. -/
theorem vector_tracelessHessian_eq_zero_on_inactive_of_weak_equation (hd : 0 < d)
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      laplaceBilin univ (U j) W =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) (W.val 0)) :
    ∀ᵐ x ∂volume, globalVectorDirichletObservation U x = 0 → ∀ j : Fin m,
      tracelessHessianL2CLM d hd (complexUnivL2
        (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)) x = 0 := by
  let q (j : Fin m) := complexUnivL2 (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)
  have hadd (j : Fin m) : ∀ᵐ x ∂volume,
      tracelessHessianL2CLM d hd (q j) x =
        hessianL2 (q j) x + identityTensorCLM d (q j x) := by
    rw [tracelessHessianL2CLM_eq_hessian_add_identity hd]
    filter_upwards [Lp.coeFn_add (hessianL2 (q j)) ((identityTensorCLM d).compLp (q j)),
      (identityTensorCLM d).coeFn_compLp (q j)] with x hx hi
    rw [hx, Pi.add_apply, hi]
  filter_upwards [vector_hessianL2_eq_zero_on_inactive_of_weak_equation U f ν hpde,
    vector_complex_residual_eq_zero_on_inactive_of_weak_equation U f ν hpde,
    ae_all_iff.mpr hadd] with x hH hq hx
  intro hu j
  rw [hx j, hH hu j, hq hu j, map_zero, add_zero]

/-- Genuine vector partial balayage supplies capped data and actual coordinate Hessian
agreement off a measurable active set, for every integrable L² input. -/
theorem exists_wholeSpace_vector_hessian_capped_decomposition
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))))
    (hf : Integrable f volume) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : Lp (EuclideanSpace ℝ (Fin m)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))))
      (s : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      MeasurableSet s ∧ ν ∈ normCap volume (κ : ℝ) ∧ Integrable ν volume ∧
      (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ ∧
      ENNReal.ofReal (κ : ℝ) * volume s ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (∀ᵐ x ∂volume, x ∉ s → ν x = f x) ∧
      (∀ᵐ x ∂volume, x ∉ s → ∀ j : Fin m,
        hessianL2 (complexUnivL2 (univVectorCoordinateCLM j f)) x =
          hessianL2 (complexUnivL2 (univVectorCoordinateCLM j ν)) x) := by
  obtain ⟨ν, U, hcap, hν, hmass, _, _, hpde, halign, _⟩ :=
    exists_wholeSpace_vectorBalayage f hf κ hκ
  have hκreal : 0 < (κ : ℝ) := by exact_mod_cast hκ
  refine ⟨ν, {x | globalVectorDirichletObservation U x ≠ 0},
    measurableSet_globalVectorDirichlet_active U, hcap, hν, ?_,
    globalVectorDirichlet_cap_measure_bound U f ν hκreal hf hν hpde halign, ?_, ?_⟩
  · rw [← ofReal_integral_norm_eq_lintegral_enorm hν,
      ← ofReal_integral_norm_eq_lintegral_enorm hf]
    exact ENNReal.ofReal_le_ofReal hmass
  · filter_upwards [vector_density_eq_input_on_inactive_of_global_weak_equation U f ν hpde]
      with x hx
    simpa only [Set.mem_ofPred_eq, not_not] using hx
  · filter_upwards [vector_hessianL2_eq_on_inactive_of_weak_equation U f ν hpde]
      with x hx
    simpa only [Set.mem_ofPred_eq, not_not] using hx

end PartialBalayage.Linear
