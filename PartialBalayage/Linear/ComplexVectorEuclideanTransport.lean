/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexEuclideanTransport

/-!
# Genuine realification of finite complex Euclidean vectors

Taking the real and imaginary coordinate of every complex component gives a real linear
isometry into a real Euclidean space of twice the dimension. The corresponding actual L²
maps preserve norm caps, integrability, and full vector mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- The pair-indexed coordinates are relabelled by the canonical finite product equivalence. -/
def complexVectorRealIndexEquiv (m : ℕ) :
    (Σ _ : Fin m, Fin 2) ≃ Fin (m * 2) :=
  (Equiv.sigmaEquivProd (Fin m) (Fin 2)).trans finProdFinEquiv

/-- The actual real-coordinate isometry for an arbitrary finite complex Euclidean vector. -/
def complexVectorEuclideanIsometry (m : ℕ) :
    EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m * 2)) :=
  (Pi.orthonormalBasis (fun _ : Fin m ↦ Complex.orthonormalBasisOneI)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (complexVectorRealIndexEquiv m))

/-- The actual real coordinate with pair index zero is the original real part. -/
theorem complexVectorEuclideanIsometry_re (v : EuclideanSpace ℂ (Fin m)) (j : Fin m) :
    complexVectorEuclideanIsometry m v (complexVectorRealIndexEquiv m ⟨j, 0⟩) =
      (v j).re := by
  simp [complexVectorEuclideanIsometry, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', Pi.orthonormalBasis, Sigma.uncurry]

/-- The actual real coordinate with pair index one is the original imaginary part. -/
theorem complexVectorEuclideanIsometry_im (v : EuclideanSpace ℂ (Fin m)) (j : Fin m) :
    complexVectorEuclideanIsometry m v (complexVectorRealIndexEquiv m ⟨j, 1⟩) =
      (v j).im := by
  simp [complexVectorEuclideanIsometry, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', Pi.orthonormalBasis, Sigma.uncurry]

/-- The inverse realification reconstructs every actual complex component. -/
theorem complexVectorEuclideanIsometry_symm_apply
    (v : EuclideanSpace ℝ (Fin (m * 2))) (j : Fin m) :
    (complexVectorEuclideanIsometry m).symm v j =
      (v (complexVectorRealIndexEquiv m ⟨j, 0⟩) : ℂ) +
        (v (complexVectorRealIndexEquiv m ⟨j, 1⟩) : ℂ) * Complex.I := by
  have hre := complexVectorEuclideanIsometry_re ((complexVectorEuclideanIsometry m).symm v) j
  have him := complexVectorEuclideanIsometry_im ((complexVectorEuclideanIsometry m).symm v) j
  rw [LinearIsometryEquiv.apply_symm_apply] at hre him
  rw [hre, him]
  exact (Complex.re_add_im _).symm

/-- The actual L² map realifying finite complex vectors. -/
def complexVectorToRealL2CLM (μ : Measure X) (m : ℕ) :
    Lp (EuclideanSpace ℂ (Fin m)) 2 μ →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin (m * 2))) 2 μ :=
  (complexVectorEuclideanIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ

/-- The actual L² map combining real vector coordinates into complex components. -/
def realToComplexVectorL2CLM (μ : Measure X) (m : ℕ) :
    Lp (EuclideanSpace ℝ (Fin (m * 2))) 2 μ →L[ℝ]
      Lp (EuclideanSpace ℂ (Fin m)) 2 μ :=
  (complexVectorEuclideanIsometry m).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 μ

theorem complexVectorToRealL2CLM_ae (μ : Measure X)
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2 μ) :
    complexVectorToRealL2CLM μ m f =ᵐ[μ] fun x ↦ complexVectorEuclideanIsometry m (f x) :=
  (complexVectorEuclideanIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

theorem realToComplexVectorL2CLM_ae (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin (m * 2))) 2 μ) :
    realToComplexVectorL2CLM μ m v =ᵐ[μ]
      fun x ↦ (complexVectorEuclideanIsometry m).symm (v x) :=
  (complexVectorEuclideanIsometry m).symm.toContinuousLinearEquiv.toContinuousLinearMap
    |>.coeFn_compLpL v

/-- Both actual L² maps are inverse on finite complex vector inputs. -/
theorem realToComplexVector_complexVectorToReal (μ : Measure X)
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2 μ) :
    realToComplexVectorL2CLM μ m (complexVectorToRealL2CLM μ m f) = f := by
  apply Lp.ext
  filter_upwards [realToComplexVectorL2CLM_ae μ (complexVectorToRealL2CLM μ m f),
    complexVectorToRealL2CLM_ae μ f] with x hb hf
  rw [hb, hf, LinearIsometryEquiv.symm_apply_apply]

/-- The genuine forward representative preserves the full Euclidean vector norm. -/
theorem complexVectorToRealL2CLM_norm_ae (μ : Measure X)
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2 μ) :
    (fun x ↦ ‖complexVectorToRealL2CLM μ m f x‖) =ᵐ[μ] fun x ↦ ‖f x‖ := by
  filter_upwards [complexVectorToRealL2CLM_ae μ f] with x hx
  rw [hx, LinearIsometryEquiv.norm_map]

/-- The genuine inverse representative preserves the full Euclidean vector norm. -/
theorem realToComplexVectorL2CLM_norm_ae (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin (m * 2))) 2 μ) :
    (fun x ↦ ‖realToComplexVectorL2CLM μ m v x‖) =ᵐ[μ] fun x ↦ ‖v x‖ := by
  filter_upwards [realToComplexVectorL2CLM_ae μ v] with x hx
  rw [hx, LinearIsometryEquiv.norm_map]

/-- Forward realification preserves full vector mass. -/
theorem lintegral_enorm_complexVectorToRealL2CLM (μ : Measure X)
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2 μ) :
    (∫⁻ x, ‖complexVectorToRealL2CLM μ m f x‖ₑ ∂μ) =
      ∫⁻ x, ‖f x‖ₑ ∂μ := by
  apply lintegral_congr_ae
  exact (complexVectorToRealL2CLM_norm_ae μ f).mono
    (fun _ hx ↦ enorm_eq_iff_norm_eq.mpr hx)

/-- Inverse realification preserves full vector mass. -/
theorem lintegral_enorm_realToComplexVectorL2CLM (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin (m * 2))) 2 μ) :
    (∫⁻ x, ‖realToComplexVectorL2CLM μ m v x‖ₑ ∂μ) =
      ∫⁻ x, ‖v x‖ₑ ∂μ := by
  apply lintegral_congr_ae
  exact (realToComplexVectorL2CLM_norm_ae μ v).mono
    (fun _ hx ↦ enorm_eq_iff_norm_eq.mpr hx)

/-- Forward realification preserves actual integrability. -/
theorem integrable_complexVectorToRealL2CLM_iff (μ : Measure X)
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2 μ) :
    Integrable (complexVectorToRealL2CLM μ m f) μ ↔ Integrable f μ := by
  rw [← integrable_norm_iff (Lp.aestronglyMeasurable (complexVectorToRealL2CLM μ m f)),
    ← integrable_norm_iff (Lp.aestronglyMeasurable f)]
  exact integrable_congr (complexVectorToRealL2CLM_norm_ae μ f)

/-- Inverse realification preserves actual integrability. -/
theorem integrable_realToComplexVectorL2CLM_iff (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin (m * 2))) 2 μ) :
    Integrable (realToComplexVectorL2CLM μ m v) μ ↔ Integrable v μ := by
  rw [← integrable_norm_iff (Lp.aestronglyMeasurable (realToComplexVectorL2CLM μ m v)),
    ← integrable_norm_iff (Lp.aestronglyMeasurable v)]
  exact integrable_congr (realToComplexVectorL2CLM_norm_ae μ v)

/-- The genuine inverse realification preserves the actual full-vector norm cap. -/
theorem realToComplexVectorL2CLM_mem_normCap_iff (μ : Measure X) (κ : ℝ)
    (v : Lp (EuclideanSpace ℝ (Fin (m * 2))) 2 μ) :
    realToComplexVectorL2CLM μ m v ∈ normCap μ κ ↔ v ∈ normCap μ κ := by
  simp only [normCap, mem_ofPred_eq]
  apply eventually_congr
  filter_upwards [realToComplexVectorL2CLM_norm_ae μ v] with x hx
  change ‖realToComplexVectorL2CLM μ m v x‖ = ‖v x‖ at hx
  rw [hx]

/-- The actual scalar complex coordinate observation. -/
def complexVectorCoordinateCLM (j : Fin m) : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : Fin m ↦ ℂ) j

theorem complexVectorCoordinateCLM_ae (μ : Measure X) (j : Fin m)
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2 μ) :
    (complexVectorCoordinateCLM j).compLp f =ᵐ[μ] fun x ↦ f x j :=
  (complexVectorCoordinateCLM j).coeFn_compLp f

section WholeSpace

variable {d : ℕ}

/-- Every actual inverse-transported complex component is exactly reconstructed from its
two real L² coordinates. -/
theorem realToComplexVectorL2CLM_coordinate_reconstruction
    (v : Lp (EuclideanSpace ℝ (Fin (m * 2))) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) (j : Fin m) :
    (complexVectorCoordinateCLM j).compLp (realToComplexVectorL2CLM volume m v) =
      complexUnivL2 (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 0⟩) v) +
        Complex.I • complexUnivL2
          (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 1⟩) v) := by
  let r := univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 0⟩) v
  let i := univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 1⟩) v
  apply Lp.ext
  filter_upwards [complexVectorCoordinateCLM_ae volume j (realToComplexVectorL2CLM volume m v),
    realToComplexVectorL2CLM_ae volume v, complexUnivL2_ae r, complexUnivL2_ae i,
    univVectorCoordinateCLM_ae (complexVectorRealIndexEquiv m ⟨j, 0⟩) v,
    univVectorCoordinateCLM_ae (complexVectorRealIndexEquiv m ⟨j, 1⟩) v,
    Lp.coeFn_add (complexUnivL2 r) (Complex.I • complexUnivL2 i),
    Lp.coeFn_smul Complex.I (complexUnivL2 i)] with x hc hb hr hi hrv hiv ha hs
  rw [hc, hb, complexVectorEuclideanIsometry_symm_apply, ha, Pi.add_apply,
    hs, Pi.smul_apply, hr, hi, hrv, hiv]
  simp only [smul_eq_mul, mul_comm]

/-- Realification reconstructs the actual scalar coordinate of every complex vector input. -/
theorem complexVectorToRealL2CLM_coordinate_reconstruction
    (f : Lp (EuclideanSpace ℂ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) (j : Fin m) :
    (complexVectorCoordinateCLM j).compLp f =
      complexUnivL2 (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 0⟩)
        (complexVectorToRealL2CLM volume m f)) +
      Complex.I • complexUnivL2
        (univVectorCoordinateCLM (complexVectorRealIndexEquiv m ⟨j, 1⟩)
          (complexVectorToRealL2CLM volume m f)) := by
  simpa only [realToComplexVector_complexVectorToReal] using
    realToComplexVectorL2CLM_coordinate_reconstruction (complexVectorToRealL2CLM volume m f) j

end WholeSpace

end PartialBalayage.Linear
