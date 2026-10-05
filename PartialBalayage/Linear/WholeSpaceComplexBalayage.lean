/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceHessianLocality
public import PartialBalayage.Linear.ComplexEuclideanTransport

/-!
# Actual complex capped decompositions with Hessian locality

The genuine real isometry between the complex plane and its two Euclidean coordinates
transports the constructed vector partial balayage. Its actual weak PDE supplies Hessian
agreement off a measurable active set, while the isometry preserves the full complex norm cap
and input mass. Every input is an arbitrary integrable complex L² function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- The genuine Hessian of the inverse complex transport is the complex combination of
the Hessians of its two actual real coordinates. -/
theorem hessianL2_euclideanToComplex_reconstruction
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    hessianL2 (euclideanToComplexL2CLM volume v) =
      hessianL2 (complexUnivL2 (univVectorCoordinateCLM 0 v)) +
        Complex.I • hessianL2 (complexUnivL2 (univVectorCoordinateCLM 1 v)) := by
  rw [euclideanToComplexL2CLM_reconstruction]
  simpa only [hessianL2CLM_apply, hessianL2_smul] using (hessianL2CLM d).map_add
    (complexUnivL2 (univVectorCoordinateCLM 0 v))
    (Complex.I • complexUnivL2 (univVectorCoordinateCLM 1 v))

/-- Pointwise reconstruction of the genuine Hessian representatives holds almost everywhere. -/
theorem hessianL2_euclideanToComplex_reconstruction_ae
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ∀ᵐ x ∂volume, hessianL2 (euclideanToComplexL2CLM volume v) x =
      hessianL2 (complexUnivL2 (univVectorCoordinateCLM 0 v)) x +
        Complex.I • hessianL2 (complexUnivL2 (univVectorCoordinateCLM 1 v)) x := by
  rw [hessianL2_euclideanToComplex_reconstruction]
  filter_upwards [Lp.coeFn_add
    (hessianL2 (complexUnivL2 (univVectorCoordinateCLM 0 v)))
    (Complex.I • hessianL2 (complexUnivL2 (univVectorCoordinateCLM 1 v))),
    Lp.coeFn_smul Complex.I (hessianL2 (complexUnivL2 (univVectorCoordinateCLM 1 v)))]
    with x hadd hsmul
  simp only [hadd, hsmul, Pi.add_apply, Pi.smul_apply]

/-- Every integrable complex L² input has genuine capped data with Hessian agreement off
a measurable set whose cap-weighted volume is bounded by the full complex input mass. -/
theorem exists_complex_hessian_capped_decomposition (hd : 0 < d)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : Integrable f volume) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (s : Set (EuclideanSpace ℝ (Fin d))),
      MeasurableSet s ∧ (∀ᵐ x ∂volume, ‖ν x‖ ≤ (κ : ℝ)) ∧
      Integrable ν volume ∧
      (∫⁻ x, ‖ν x‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ ∧
      ENNReal.ofReal (κ : ℝ) * volume s ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (∀ᵐ x ∂volume, x ∉ s → ν x = f x) ∧
      (∀ᵐ x ∂volume, x ∉ s → hessianL2 f x = hessianL2 ν x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let F := complexToEuclideanL2CLM volume f
  have hF : Integrable F volume := (integrable_complexToEuclideanL2CLM_iff volume f).mpr hf
  obtain ⟨v, s, hs, hv, hvint, hmass, hs_mass, hinactive, hH⟩ :=
    exists_wholeSpace_vector_hessian_capped_decomposition F hF κ hκ
  let ν := euclideanToComplexL2CLM volume v
  have hνcap : ν ∈ normCap volume (κ : ℝ) :=
    (euclideanToComplexL2CLM_mem_normCap_iff volume (κ : ℝ) v).mpr hv
  have hνint : Integrable ν volume :=
    (integrable_euclideanToComplexL2CLM_iff volume v).mpr hvint
  refine ⟨ν, s, hs, hνcap, hνint, ?_, ?_, ?_, ?_⟩
  · simpa only [ν, F, lintegral_enorm_euclideanToComplexL2CLM,
      lintegral_enorm_complexToEuclideanL2CLM] using hmass
  · simpa only [F, lintegral_enorm_complexToEuclideanL2CLM] using hs_mass
  · filter_upwards [euclideanToComplexL2CLM_ae volume v,
      complexToEuclideanL2CLM_ae volume f, hinactive] with x hvx hfx hx
    intro hxs
    change euclideanToComplexL2CLM volume v x = f x
    rw [hvx, hx hxs, hfx, complexEuclideanIsometry.symm_apply_apply]
  · have hback : euclideanToComplexL2CLM volume F = f :=
      euclideanToComplex_complexToEuclidean volume f
    have hFh := hessianL2_euclideanToComplex_reconstruction_ae F
    rw [hback] at hFh
    filter_upwards [hFh, hessianL2_euclideanToComplex_reconstruction_ae v, hH]
      with x hfx hvx hx
    intro hxs
    change hessianL2 f x = hessianL2 (euclideanToComplexL2CLM volume v) x
    rw [hfx, hvx, hx hxs 0, hx hxs 1]

/-- Actual Hessian and input agreement imply actual traceless-Hessian agreement off the set. -/
theorem tracelessHessian_eq_off_of_hessian_eq (hd : 0 < d)
    (f ν : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hinput : ∀ᵐ x ∂volume, x ∉ s → ν x = f x)
    (hH : ∀ᵐ x ∂volume, x ∉ s → hessianL2 f x = hessianL2 ν x) :
    ∀ᵐ x ∂volume, x ∉ s →
      tracelessHessianL2CLM d hd f x = tracelessHessianL2CLM d hd ν x := by
  have hsplit (q : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
      ∀ᵐ x ∂volume, tracelessHessianL2CLM d hd q x =
        hessianL2 q x + identityTensorCLM d (q x) := by
    rw [tracelessHessianL2CLM_eq_hessian_add_identity hd]
    filter_upwards [Lp.coeFn_add (hessianL2 q) ((identityTensorCLM d).compLp q),
      (identityTensorCLM d).coeFn_compLp q] with x ha hi
    simp only [ha, hi, Pi.add_apply]
  filter_upwards [hsplit f, hsplit ν, hinput, hH] with x hf hν hx hh
  intro hs
  rw [hf, hν, hx hs, hh hs]

/-- Actual Hessian agreement implies actual Beurling agreement off the same set. -/
theorem beurling_eq_off_of_hessian_eq
    (f ν : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hH : ∀ᵐ x ∂volume, x ∉ s → hessianL2 f x = hessianL2 ν x) :
    ∀ᵐ x ∂volume, x ∉ s → beurlingL2 f x = beurlingL2 ν x := by
  rw [beurlingL2_eq_hessian_combination, beurlingL2_eq_hessian_combination]
  filter_upwards [beurlingHessianCombination.coeFn_compLp (hessianL2 f),
    beurlingHessianCombination.coeFn_compLp (hessianL2 ν), hH] with x hf hν hh
  intro hs
  rw [hf, hν, hh hs]

end PartialBalayage.Linear
