/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceHessianLocality
public import PartialBalayage.Linear.ComplexVectorEuclideanTransport
public import PartialBalayage.Linear.ProjectionHessianIdentity

/-!
# Actual complex vector partial balayage for the projection operators

The norm-preserving realification transports the genuine vector obstacle to arbitrary complex
Euclidean vector inputs. Its true PDE gives Hessian agreement in every complex coordinate off
the measured active set. The genuine Hessian identities then give cancellation for the gradient
and Leray projections and their shifted operators.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {d m : ℕ}

/-- The actual Hessian of an inverse-realified scalar coordinate is reconstructed from its
two real scalar coordinate Hessians, with almost-everywhere representatives. -/
theorem hessianL2_realToComplexVector_coordinate_reconstruction_ae
    (v : Lp (EuclideanSpace ℝ (Fin (m * 2))) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) (j : Fin m) :
    ∀ᵐ x ∂volume,
      hessianL2 ((complexVectorCoordinateCLM j).compLp (realToComplexVectorL2CLM volume m v)) x =
        hessianL2 (complexUnivL2
          (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 0⟩) v)) x +
        Complex.I • hessianL2 (complexUnivL2
          (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 1⟩) v)) x := by
  let r := complexUnivL2 (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 0⟩) v)
  let i := complexUnivL2 (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 1⟩) v)
  have hsum : hessianL2 (r + Complex.I • i) = hessianL2 r + Complex.I • hessianL2 i := by
    simpa only [hessianL2CLM_apply, hessianL2_smul] using
      (hessianL2CLM d).map_add r (Complex.I • i)
  rw [realToComplexVectorL2CLM_coordinate_reconstruction, hsum]
  filter_upwards [Lp.coeFn_add (hessianL2 r) (Complex.I • hessianL2 i),
    Lp.coeFn_smul Complex.I (hessianL2 i)] with x ha hs
  simp only [ha, hs, Pi.add_apply, Pi.smul_apply, r, i]

/-- Arbitrary integrable complex Euclidean vector inputs admit actual capped data with
every scalar coordinate Hessian agreeing off the measurable active set. -/
theorem exists_complexVector_hessian_capped_decomposition (hd : 0 < d)
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : Integrable f volume) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : Lp (EuclideanSpace ℂ (Fin m)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (s : Set (EuclideanSpace ℝ (Fin d))),
      MeasurableSet s ∧ (∀ᵐ x ∂volume, ‖ν x‖ ≤ (κ : ℝ)) ∧
      Integrable ν volume ∧ (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ ∧
      ENNReal.ofReal (κ : ℝ) * volume s ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (∀ᵐ x ∂volume, x ∉ s → ν x = f x) ∧
      (∀ᵐ x ∂volume, x ∉ s → ∀ j : Fin m,
        hessianL2 ((complexVectorCoordinateCLM j).compLp f) x =
          hessianL2 ((complexVectorCoordinateCLM j).compLp ν) x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let F := complexVectorToRealL2CLM volume m f
  have hF : Integrable F volume := (integrable_complexVectorToRealL2CLM_iff volume f).mpr hf
  obtain ⟨v, s, hs, hv, hvint, hmass, hs_mass, hinactive, hH⟩ :=
    exists_wholeSpace_vector_hessian_capped_decomposition F hF κ hκ
  let ν := realToComplexVectorL2CLM volume m v
  have hνcap : ν ∈ normCap volume (κ : ℝ) :=
    (realToComplexVectorL2CLM_mem_normCap_iff volume (κ : ℝ) v).mpr hv
  have hνint : Integrable ν volume :=
    (integrable_realToComplexVectorL2CLM_iff volume v).mpr hvint
  refine ⟨ν, s, hs, hνcap, hνint, ?_, ?_, ?_, ?_⟩
  · simpa only [ν, F, lintegral_enorm_realToComplexVectorL2CLM,
      lintegral_enorm_complexVectorToRealL2CLM] using hmass
  · simpa only [F, lintegral_enorm_complexVectorToRealL2CLM] using hs_mass
  · filter_upwards [realToComplexVectorL2CLM_ae volume v,
      complexVectorToRealL2CLM_ae volume f, hinactive] with x hvx hfx hx
    intro hxs
    change realToComplexVectorL2CLM volume m v x = f x
    rw [hvx, hx hxs, hfx, LinearIsometryEquiv.symm_apply_apply]
  · have hback : realToComplexVectorL2CLM volume m F = f :=
      realToComplexVector_complexVectorToReal volume f
    have hFh := ae_all_iff.mpr (hessianL2_realToComplexVector_coordinate_reconstruction_ae F)
    rw [hback] at hFh
    filter_upwards [hFh,
      ae_all_iff.mpr (hessianL2_realToComplexVector_coordinate_reconstruction_ae v), hH]
      with x hfx hvx hx
    intro hxs j
    change hessianL2 ((complexVectorCoordinateCLM j).compLp f) x =
      hessianL2 ((complexVectorCoordinateCLM j).compLp
        (realToComplexVectorL2CLM volume m v)) x
    rw [hfx j, hvx j, hx hxs _, hx hxs _]

/-- The actual gradient projection representative is the negative Hessian row sum. -/
theorem gradientProjectionL2_ae_eq_neg_sum_hessian
    (f : Lp (EuclideanSpace ℂ (Fin d)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) (i : Fin d) :
    ∀ᵐ x ∂volume, gradientProjectionL2CLM f x i =
      -∑ j : Fin d, hessianL2 ((projectionCoordinateCLM j).compLp f) x (i, j) := by
  let term (j : Fin d) := (hessianEntryCLM i j).compLp
    (hessianL2 ((projectionCoordinateCLM j).compLp f))
  have hc := projectionCoordinateCLM_ae (gradientProjectionL2CLM f) i
  rw [gradientProjectionL2_coordinate_eq_neg_sum_hessian] at hc
  filter_upwards [hc, Lp.coeFn_neg (∑ j, term j),
    Lp.coeFn_fun_finsetSum Finset.univ term,
    ae_all_iff.mpr (fun j ↦ (hessianEntryCLM i j).coeFn_compLp
      (hessianL2 ((projectionCoordinateCLM j).compLp f)))] with x hcoord hn hs hh
  rw [hn, Pi.neg_apply, hs] at hcoord
  rw [← hcoord]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact hh j

/-- Actual scalar coordinate Hessian agreement forces actual gradient projection agreement. -/
theorem gradientProjection_eq_off_of_coordinate_hessian_eq
    (f ν : Lp (EuclideanSpace ℂ (Fin d)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hH : ∀ᵐ x ∂volume, x ∉ s → ∀ j : Fin d,
      hessianL2 ((complexVectorCoordinateCLM j).compLp f) x =
        hessianL2 ((complexVectorCoordinateCLM j).compLp ν) x) :
    ∀ᵐ x ∂volume, x ∉ s → gradientProjectionL2CLM f x = gradientProjectionL2CLM ν x := by
  filter_upwards [ae_all_iff.mpr (gradientProjectionL2_ae_eq_neg_sum_hessian f),
    ae_all_iff.mpr (gradientProjectionL2_ae_eq_neg_sum_hessian ν), hH] with x hf hν hh
  intro hs
  ext i
  rw [hf i, hν i]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : EuclideanSpace ℂ (Fin d × Fin d) ↦ v (i, j)) (hh hs j)

/-- Input and actual gradient projection agreement imply actual Leray agreement. -/
theorem lerayProjection_eq_off_of_input_and_gradient_eq
    (f ν : Lp (EuclideanSpace ℂ (Fin d)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hinput : ∀ᵐ x ∂volume, x ∉ s → ν x = f x)
    (hG : ∀ᵐ x ∂volume, x ∉ s →
      gradientProjectionL2CLM f x = gradientProjectionL2CLM ν x) :
    ∀ᵐ x ∂volume, x ∉ s → lerayProjectionL2CLM f x = lerayProjectionL2CLM ν x := by
  rw [lerayProjectionL2CLM_eq_sub_gradient]
  simp only [sub_apply, ContinuousLinearMap.id_apply]
  filter_upwards [Lp.coeFn_sub f (gradientProjectionL2CLM f),
    Lp.coeFn_sub ν (gradientProjectionL2CLM ν), hinput, hG] with x hf hν hi hGx
  intro hs
  simp only [hf, hν, Pi.sub_apply, hi hs, hGx hs]

/-- Removing half the identity preserves agreement off the set for a genuine L² operator. -/
theorem shiftedL2Operator_eq_off_of_input_and_operator_eq
    (T : Lp (EuclideanSpace ℂ (Fin d)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin d)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (f ν : Lp (EuclideanSpace ℂ (Fin d)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hinput : ∀ᵐ x ∂volume, x ∉ s → ν x = f x)
    (hT : ∀ᵐ x ∂volume, x ∉ s → T f x = T ν x) :
    ∀ᵐ x ∂volume, x ∉ s →
      (T - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ
        (Lp (EuclideanSpace ℂ (Fin d)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin d))))) f x =
        (T - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ
          (Lp (EuclideanSpace ℂ (Fin d)) 2
            (volume : Measure (EuclideanSpace ℝ (Fin d))))) ν x := by
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  filter_upwards [Lp.coeFn_sub (T f) ((1 / 2 : ℂ) • f),
    Lp.coeFn_sub (T ν) ((1 / 2 : ℂ) • ν), Lp.coeFn_smul (1 / 2 : ℂ) f,
    Lp.coeFn_smul (1 / 2 : ℂ) ν, hinput, hT] with x hf hν hsf hsν hi hx
  intro hs
  simp only [hf, hν, Pi.sub_apply, hsf, hsν, Pi.smul_apply, hi hs, hx hs]

/-- Genuine capped partial balayage gives agreement off one measured active set for both
actual projections and both actual shifted projections on arbitrary complex vector inputs. -/
theorem exists_complexVector_projection_capped_decomposition (hd : 0 < d)
    (f : Lp (EuclideanSpace ℂ (Fin d)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : Integrable f volume) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : Lp (EuclideanSpace ℂ (Fin d)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (s : Set (EuclideanSpace ℝ (Fin d))),
      MeasurableSet s ∧ (∀ᵐ x ∂volume, ‖ν x‖ ≤ (κ : ℝ)) ∧
      Integrable ν volume ∧ (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ ∧
      ENNReal.ofReal (κ : ℝ) * volume s ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (∀ᵐ x ∂volume, x ∉ s → ν x = f x) ∧
      (∀ᵐ x ∂volume, x ∉ s →
        gradientProjectionL2CLM f x = gradientProjectionL2CLM ν x) ∧
      (∀ᵐ x ∂volume, x ∉ s → lerayProjectionL2CLM f x = lerayProjectionL2CLM ν x) ∧
      (∀ᵐ x ∂volume, x ∉ s →
        shiftedGradientProjectionL2CLM f x = shiftedGradientProjectionL2CLM ν x) ∧
      (∀ᵐ x ∂volume, x ∉ s →
        shiftedLerayProjectionL2CLM f x = shiftedLerayProjectionL2CLM ν x) := by
  obtain ⟨ν, s, hs, hcap, hν, hmass, hs_mass, hinput, hH⟩ :=
    exists_complexVector_hessian_capped_decomposition hd f hf κ hκ
  have hG := gradientProjection_eq_off_of_coordinate_hessian_eq f ν hH
  have hL := lerayProjection_eq_off_of_input_and_gradient_eq f ν hinput hG
  refine ⟨ν, s, hs, hcap, hν, hmass, hs_mass, hinput, hG, hL, ?_, ?_⟩
  · rw [shiftedGradientProjectionL2CLM_eq_sub_half]
    exact shiftedL2Operator_eq_off_of_input_and_operator_eq _ f ν hinput hG
  · rw [shiftedLerayProjectionL2CLM_eq_sub_half]
    exact shiftedL2Operator_eq_off_of_input_and_operator_eq _ f ν hinput hL

end PartialBalayage.Linear
