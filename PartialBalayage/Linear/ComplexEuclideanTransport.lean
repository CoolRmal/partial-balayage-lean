/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.SchwartzDirichletTest
public import PartialBalayage.Linear.ExhaustionWeakEquation
public import PartialBalayage.Linear.WholeSpaceMassCompactness

/-!
# Actual complex and two-coordinate Euclidean transport

The existing orthonormal basis `1, I` gives a genuine real linear isometry. Its actual `L²`
composition maps preserve pointwise norms, full mass, integrability, and norm caps. Whole-space
coordinate extraction and complexification recover the actual real and imaginary input parts.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X : Type*} [MeasurableSpace X]

/-- The actual orthonormal real-coordinate isometry for the complex plane. -/
def complexEuclideanIsometry : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

/-- The actual `L²` map taking a complex function to its two real Euclidean coordinates. -/
def complexToEuclideanL2CLM (μ : Measure X) :
    Lp ℂ 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 2)) 2 μ :=
  complexEuclideanIsometry.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ

/-- The actual `L²` map combining two real Euclidean coordinates into a complex function. -/
def euclideanToComplexL2CLM (μ : Measure X) :
    Lp (EuclideanSpace ℝ (Fin 2)) 2 μ →L[ℝ] Lp ℂ 2 μ :=
  complexEuclideanIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ

/-- The forward `L²` transport agrees almost everywhere with the genuine pointwise isometry. -/
theorem complexToEuclideanL2CLM_ae (μ : Measure X) (f : Lp ℂ 2 μ) :
    complexToEuclideanL2CLM μ f =ᵐ[μ] fun x ↦ complexEuclideanIsometry (f x) :=
  complexEuclideanIsometry.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

/-- The reverse `L²` transport agrees almost everywhere with the genuine inverse isometry. -/
theorem euclideanToComplexL2CLM_ae (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    euclideanToComplexL2CLM μ v =ᵐ[μ] fun x ↦ complexEuclideanIsometry.symm (v x) :=
  complexEuclideanIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL v

/-- The actual forward map has real part in coordinate zero. -/
theorem complexToEuclideanL2CLM_zero_ae (μ : Measure X) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, complexToEuclideanL2CLM μ f x 0 = (f x).re := by
  filter_upwards [complexToEuclideanL2CLM_ae μ f] with x hx
  rw [hx]
  simp [complexEuclideanIsometry]

/-- The actual forward map has imaginary part in coordinate one. -/
theorem complexToEuclideanL2CLM_one_ae (μ : Measure X) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, complexToEuclideanL2CLM μ f x 1 = (f x).im := by
  filter_upwards [complexToEuclideanL2CLM_ae μ f] with x hx
  rw [hx]
  simp [complexEuclideanIsometry]

/-- The inverse transport reconstructs the actual complex value from the two real coordinates. -/
theorem euclideanToComplexL2CLM_value_ae (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    euclideanToComplexL2CLM μ v =ᵐ[μ] fun x ↦ (v x 0 : ℂ) + (v x 1 : ℂ) * Complex.I := by
  filter_upwards [euclideanToComplexL2CLM_ae μ v] with x hx
  rw [hx]
  exact Complex.orthonormalBasisOneI_repr_symm_apply (v x)

/-- The two actual composition maps are inverses on complex `L²`. -/
theorem euclideanToComplex_complexToEuclidean (μ : Measure X) (f : Lp ℂ 2 μ) :
    euclideanToComplexL2CLM μ (complexToEuclideanL2CLM μ f) = f := by
  apply Lp.ext
  filter_upwards [euclideanToComplexL2CLM_ae μ (complexToEuclideanL2CLM μ f),
    complexToEuclideanL2CLM_ae μ f] with x hback hforward
  rw [hback, hforward, complexEuclideanIsometry.symm_apply_apply]

/-- The two actual composition maps are inverses on Euclidean-valued `L²`. -/
theorem complexToEuclidean_euclideanToComplex (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    complexToEuclideanL2CLM μ (euclideanToComplexL2CLM μ v) = v := by
  apply Lp.ext
  filter_upwards [complexToEuclideanL2CLM_ae μ (euclideanToComplexL2CLM μ v),
    euclideanToComplexL2CLM_ae μ v] with x hforward hback
  rw [hforward, hback, complexEuclideanIsometry.apply_symm_apply]

/-- Forward transport preserves the genuine pointwise norm almost everywhere. -/
theorem complexToEuclideanL2CLM_norm_ae (μ : Measure X) (f : Lp ℂ 2 μ) :
    (fun x ↦ ‖complexToEuclideanL2CLM μ f x‖) =ᵐ[μ] fun x ↦ ‖f x‖ := by
  filter_upwards [complexToEuclideanL2CLM_ae μ f] with x hx
  rw [hx, complexEuclideanIsometry.norm_map]

/-- Reverse transport preserves the genuine pointwise norm almost everywhere. -/
theorem euclideanToComplexL2CLM_norm_ae (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    (fun x ↦ ‖euclideanToComplexL2CLM μ v x‖) =ᵐ[μ] fun x ↦ ‖v x‖ := by
  filter_upwards [euclideanToComplexL2CLM_ae μ v] with x hx
  rw [hx, complexEuclideanIsometry.symm.norm_map]

/-- Forward transport preserves the extended pointwise norm almost everywhere. -/
theorem complexToEuclideanL2CLM_enorm_ae (μ : Measure X) (f : Lp ℂ 2 μ) :
    (fun x ↦ ‖complexToEuclideanL2CLM μ f x‖ₑ) =ᵐ[μ] fun x ↦ ‖f x‖ₑ :=
  (complexToEuclideanL2CLM_norm_ae μ f).mono fun _ hx ↦ enorm_eq_iff_norm_eq.mpr hx

/-- Reverse transport preserves the extended pointwise norm almost everywhere. -/
theorem euclideanToComplexL2CLM_enorm_ae (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    (fun x ↦ ‖euclideanToComplexL2CLM μ v x‖ₑ) =ᵐ[μ] fun x ↦ ‖v x‖ₑ :=
  (euclideanToComplexL2CLM_norm_ae μ v).mono fun _ hx ↦ enorm_eq_iff_norm_eq.mpr hx

/-- Forward transport preserves the actual Hilbert `L²` norm. -/
theorem norm_complexToEuclideanL2CLM (μ : Measure X) (f : Lp ℂ 2 μ) :
    ‖complexToEuclideanL2CLM μ f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      (complexToEuclideanL2CLM_norm_ae μ f)]

/-- Reverse transport preserves the actual Hilbert `L²` norm. -/
theorem norm_euclideanToComplexL2CLM (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    ‖euclideanToComplexL2CLM μ v‖ = ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      (euclideanToComplexL2CLM_norm_ae μ v)]

/-- Forward transport preserves the full ordinary norm mass. -/
theorem integral_norm_complexToEuclideanL2CLM (μ : Measure X) (f : Lp ℂ 2 μ) :
    (∫ x, ‖complexToEuclideanL2CLM μ f x‖ ∂μ) = ∫ x, ‖f x‖ ∂μ :=
  integral_congr_ae (complexToEuclideanL2CLM_norm_ae μ f)

/-- Reverse transport preserves the full ordinary norm mass. -/
theorem integral_norm_euclideanToComplexL2CLM (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    (∫ x, ‖euclideanToComplexL2CLM μ v x‖ ∂μ) = ∫ x, ‖v x‖ ∂μ :=
  integral_congr_ae (euclideanToComplexL2CLM_norm_ae μ v)

/-- Forward transport preserves full extended norm mass, including infinite mass. -/
theorem lintegral_enorm_complexToEuclideanL2CLM (μ : Measure X) (f : Lp ℂ 2 μ) :
    (∫⁻ x, ‖complexToEuclideanL2CLM μ f x‖ₑ ∂μ) = ∫⁻ x, ‖f x‖ₑ ∂μ :=
  lintegral_congr_ae (complexToEuclideanL2CLM_enorm_ae μ f)

/-- Reverse transport preserves full extended norm mass, including infinite mass. -/
theorem lintegral_enorm_euclideanToComplexL2CLM (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    (∫⁻ x, ‖euclideanToComplexL2CLM μ v x‖ₑ ∂μ) = ∫⁻ x, ‖v x‖ₑ ∂μ :=
  lintegral_congr_ae (euclideanToComplexL2CLM_enorm_ae μ v)

/-- Actual forward transport preserves ordinary integrability. -/
theorem integrable_complexToEuclideanL2CLM_iff (μ : Measure X) (f : Lp ℂ 2 μ) :
    Integrable (complexToEuclideanL2CLM μ f : X → EuclideanSpace ℝ (Fin 2)) μ ↔
      Integrable (f : X → ℂ) μ := by
  rw [← integrable_norm_iff (Lp.aestronglyMeasurable (complexToEuclideanL2CLM μ f)),
    ← integrable_norm_iff (Lp.aestronglyMeasurable f)]
  exact integrable_congr (complexToEuclideanL2CLM_norm_ae μ f)

/-- Actual reverse transport preserves ordinary integrability. -/
theorem integrable_euclideanToComplexL2CLM_iff (μ : Measure X)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    Integrable (euclideanToComplexL2CLM μ v : X → ℂ) μ ↔
      Integrable (v : X → EuclideanSpace ℝ (Fin 2)) μ := by
  rw [← integrable_norm_iff (Lp.aestronglyMeasurable (euclideanToComplexL2CLM μ v)),
    ← integrable_norm_iff (Lp.aestronglyMeasurable v)]
  exact integrable_congr (euclideanToComplexL2CLM_norm_ae μ v)

/-- Forward transport preserves the actual almost-everywhere norm cap. -/
theorem complexToEuclideanL2CLM_mem_normCap_iff (μ : Measure X) (κ : ℝ) (f : Lp ℂ 2 μ) :
    complexToEuclideanL2CLM μ f ∈ normCap μ κ ↔ f ∈ normCap μ κ := by
  simp only [normCap, mem_ofPred_eq]
  apply eventually_congr
  filter_upwards [complexToEuclideanL2CLM_norm_ae μ f] with x hx
  change ‖complexToEuclideanL2CLM μ f x‖ = ‖f x‖ at hx
  rw [hx]

/-- Reverse transport preserves the actual almost-everywhere norm cap. -/
theorem euclideanToComplexL2CLM_mem_normCap_iff (μ : Measure X) (κ : ℝ)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    euclideanToComplexL2CLM μ v ∈ normCap μ κ ↔ v ∈ normCap μ κ := by
  simp only [normCap, mem_ofPred_eq]
  apply eventually_congr
  filter_upwards [euclideanToComplexL2CLM_norm_ae μ v] with x hx
  change ‖euclideanToComplexL2CLM μ v x‖ = ‖v x‖ at hx
  rw [hx]

/-- Forward transport preserves genuine capped full-vector mass sets. -/
theorem complexToEuclideanL2CLM_mem_normMassCap_iff (μ : Measure X) (κ mass : ℝ≥0)
    (f : Lp ℂ 2 μ) :
    complexToEuclideanL2CLM μ f ∈ normMassCap μ κ mass ↔ f ∈ normMassCap μ κ mass := by
  simp only [normMassCap, mem_ofPred_eq, complexToEuclideanL2CLM_mem_normCap_iff,
    lintegral_enorm_complexToEuclideanL2CLM]

/-- Reverse transport preserves genuine capped full-vector mass sets. -/
theorem euclideanToComplexL2CLM_mem_normMassCap_iff (μ : Measure X) (κ mass : ℝ≥0)
    (v : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) :
    euclideanToComplexL2CLM μ v ∈ normMassCap μ κ mass ↔ v ∈ normMassCap μ κ mass := by
  simp only [normMassCap, mem_ofPred_eq, euclideanToComplexL2CLM_mem_normCap_iff,
    lintegral_enorm_euclideanToComplexL2CLM]

section WholeSpace

variable {d : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin d)
local notation "C²" => Lp ℂ 2 (volume : Measure D)
local notation "V²" => Lp (EuclideanSpace ℝ (Fin 2)) 2 (volume : Measure D)

/-- Actual whole-space scalar extraction of coordinate zero recovers the real input part. -/
theorem univVectorCoordinate_complexToEuclidean_zero_ae (f : C²) :
    univVectorCoordinateCLM 0 (complexToEuclideanL2CLM volume f) =ᵐ[volume]
      fun x ↦ (f x).re :=
  (univVectorCoordinateCLM_ae 0 _).trans (complexToEuclideanL2CLM_zero_ae volume f)

/-- Actual whole-space scalar extraction of coordinate one recovers the imaginary input part. -/
theorem univVectorCoordinate_complexToEuclidean_one_ae (f : C²) :
    univVectorCoordinateCLM 1 (complexToEuclideanL2CLM volume f) =ᵐ[volume]
      fun x ↦ (f x).im :=
  (univVectorCoordinateCLM_ae 1 _).trans (complexToEuclideanL2CLM_one_ae volume f)

/-- Coordinate zero is the genuine restricted real-part `L²` composition class. -/
theorem univVectorCoordinate_complexToEuclidean_zero (f : C²) :
    univVectorCoordinateCLM 0 (complexToEuclideanL2CLM volume f) =
      Complex.reCLM.compLp (restrictL2CLM (univ : Set D) f) := by
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have hr := restrictL2CLM_ae (univ : Set D) f
  have hc := Complex.reCLM.coeFn_compLp (restrictL2CLM (univ : Set D) f)
  simp only [Measure.restrict_univ] at hr hc
  filter_upwards [univVectorCoordinate_complexToEuclidean_zero_ae f, hr, hc]
    with x hcoord hrestrict hreal
  rw [hcoord, hreal, hrestrict]
  rfl

/-- Coordinate one is the genuine restricted imaginary-part `L²` composition class. -/
theorem univVectorCoordinate_complexToEuclidean_one (f : C²) :
    univVectorCoordinateCLM 1 (complexToEuclideanL2CLM volume f) =
      Complex.imCLM.compLp (restrictL2CLM (univ : Set D) f) := by
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have hr := restrictL2CLM_ae (univ : Set D) f
  have hc := Complex.imCLM.coeFn_compLp (restrictL2CLM (univ : Set D) f)
  simp only [Measure.restrict_univ] at hr hc
  filter_upwards [univVectorCoordinate_complexToEuclidean_one_ae f, hr, hc]
    with x hcoord hrestrict himag
  rw [hcoord, himag, hrestrict]
  rfl

/-- The genuine inverse map is exactly the complexification of the two actual scalar coordinates. -/
theorem euclideanToComplexL2CLM_reconstruction (v : V²) :
    euclideanToComplexL2CLM volume v =
      complexUnivL2 (univVectorCoordinateCLM 0 v) +
        Complex.I • complexUnivL2 (univVectorCoordinateCLM 1 v) := by
  apply Lp.ext
  filter_upwards [euclideanToComplexL2CLM_value_ae volume v,
    complexUnivL2_ae (univVectorCoordinateCLM 0 v),
    complexUnivL2_ae (univVectorCoordinateCLM 1 v),
    univVectorCoordinateCLM_ae 0 v, univVectorCoordinateCLM_ae 1 v,
    Lp.coeFn_add (complexUnivL2 (univVectorCoordinateCLM 0 v))
      (Complex.I • complexUnivL2 (univVectorCoordinateCLM 1 v)),
    Lp.coeFn_smul Complex.I (complexUnivL2 (univVectorCoordinateCLM 1 v))]
    with x hvalue hzero hone hcoordzero hcoordone hadd hsmul
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsmul
  rw [hvalue, hadd, hsmul, hzero, hone, hcoordzero, hcoordone]
  ring

/-- Genuine complex input reconstruction after actual Euclidean transport. -/
theorem complexToEuclideanL2CLM_reconstruction (f : C²) :
    f = complexUnivL2 (univVectorCoordinateCLM 0 (complexToEuclideanL2CLM volume f)) +
      Complex.I • complexUnivL2 (univVectorCoordinateCLM 1
        (complexToEuclideanL2CLM volume f)) := by
  exact (euclideanToComplex_complexToEuclidean volume f).symm.trans
    (euclideanToComplexL2CLM_reconstruction _)

end WholeSpace

end PartialBalayage.Linear
