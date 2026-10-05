/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonMarkovEnergy
public import PartialBalayage.Linear.L2DomainRestriction

/-!
# Genuine real isotropic zero-exterior energy states

The real-valued and zero-exterior conditions are kernels of actual bounded `L²` maps.
Their intersection is a complete real Hilbert subspace of the isotropic half-order graph.
Actual value and energy-data maps read its physical value and full frequency-norm energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)

/-- The actual scalar complex Fourier graph, viewed with real scalars. -/
abbrev IsotropicScalarEnergy (α : ℝ) := IsotropicEnergySpace (X := D) (E := ℂ) α

instance isotropicScalarEnergyRealInner (α : ℝ) :
    InnerProductSpace ℝ (IsotropicScalarEnergy (n := n) α) :=
  InnerProductSpace.complexToReal

/-- The actual real-value observation of a scalar isotropic energy state. -/
def isotropicScalarRealValue (α : ℝ) : IsotropicScalarEnergy (n := n) α →L[ℝ] L²ℝ :=
  Complex.reCLM.compLpL 2 volume ∘L (isotropicEnergyValue α).restrictScalars ℝ

/-- The actual imaginary-value observation. -/
def isotropicScalarImagValue (α : ℝ) : IsotropicScalarEnergy (n := n) α →L[ℝ] L²ℝ :=
  Complex.imCLM.compLpL 2 volume ∘L (isotropicEnergyValue α).restrictScalars ℝ

/-- The genuine real-valued zero-exterior half-order subspace. -/
def isotropicRealSupported (Ω : Set D) : Submodule ℝ (IsotropicScalarEnergy (n := n) 1) :=
  LinearMap.ker (isotropicScalarImagValue 1).toLinearMap ⊓
    LinearMap.ker (restrictL2CLM Ωᶜ ∘L
      (isotropicEnergyValue 1).restrictScalars ℝ).toLinearMap

theorem isClosed_isotropicRealSupported (Ω : Set D) :
    IsClosed (isotropicRealSupported Ω : Set (IsotropicScalarEnergy (n := n) 1)) :=
  (ContinuousLinearMap.isClosed_ker _).inter (ContinuousLinearMap.isClosed_ker _)

/-- The actual scalar real zero-exterior domain of the isotropic square-root Laplacian. -/
abbrev IsotropicDirichletState (Ω : Set D) := ↥(isotropicRealSupported Ω)

instance (Ω : Set D) : CompleteSpace (IsotropicDirichletState Ω) :=
  (isClosed_isotropicRealSupported Ω).completeSpace_coe

theorem isotropicScalarRealValue_ae (α : ℝ) (U : IsotropicScalarEnergy (n := n) α) :
    isotropicScalarRealValue α U =ᵐ[volume] fun x ↦ (isotropicEnergyValue α U x).re :=
  Complex.reCLM.coeFn_compLp (isotropicEnergyValue α U)

theorem isotropicScalarImagValue_ae (α : ℝ) (U : IsotropicScalarEnergy (n := n) α) :
    isotropicScalarImagValue α U =ᵐ[volume] fun x ↦ (isotropicEnergyValue α U x).im :=
  Complex.imCLM.coeFn_compLp (isotropicEnergyValue α U)

/-- Kernel membership is exactly actual real-valuedness and zero exterior almost everywhere. -/
theorem mem_isotropicRealSupported_iff {Ω : Set D} (hΩ : MeasurableSet Ω)
    (U : IsotropicScalarEnergy (n := n) 1) :
    U ∈ isotropicRealSupported Ω ↔
      (∀ᵐ x, (isotropicEnergyValue 1 U x).im = 0) ∧
      (∀ᵐ x, x ∉ Ω → isotropicEnergyValue 1 U x = 0) := by
  change isotropicScalarImagValue 1 U = 0 ∧
    restrictL2CLM Ωᶜ (isotropicEnergyValue 1 U) = 0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero, Lp.eq_zero_iff_ae_eq_zero]
  have him := isotropicScalarImagValue_ae 1 U
  have hr := restrictL2CLM_ae Ωᶜ (isotropicEnergyValue 1 U)
  constructor
  · rintro ⟨hi, hs⟩
    exact ⟨him.symm.trans hi, (ae_restrict_iff' hΩ.compl).mp (hr.symm.trans hs)⟩
  · rintro ⟨hi, hs⟩
    exact ⟨him.trans hi, hr.trans ((ae_restrict_iff' hΩ.compl).mpr hs)⟩

/-- The genuine whole-space real value of an isotropic Dirichlet state. -/
def isotropicDirichletGlobalValue (Ω : Set D) : IsotropicDirichletState Ω →L[ℝ] L²ℝ :=
  isotropicScalarRealValue 1 ∘L (isotropicRealSupported Ω).subtypeL

/-- The actual restricted observation used for a finite-domain obstacle. -/
def isotropicDirichletValue (Ω : Set D) :
    IsotropicDirichletState Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  restrictL2CLM Ω ∘L isotropicDirichletGlobalValue Ω

/-- The actual isotropic half-order Fourier data, restricted to real state scalars. -/
def isotropicDirichletData (Ω : Set D) : IsotropicDirichletState Ω →L[ℝ] L²ℂ :=
  (isotropicEnergyData 1).restrictScalars ℝ ∘L (isotropicRealSupported Ω).subtypeL

theorem isotropicDirichletGlobalValue_ae {Ω : Set D} (U : IsotropicDirichletState Ω) :
    isotropicDirichletGlobalValue Ω U =ᵐ[volume]
      fun x ↦ (isotropicEnergyValue 1 U.val x).re :=
  isotropicScalarRealValue_ae 1 U.val

/-- The actual global value vanishes outside the obstacle domain. -/
theorem isotropicDirichletGlobalValue_zero_exterior {Ω : Set D} (hΩ : MeasurableSet Ω)
    (U : IsotropicDirichletState Ω) :
    ∀ᵐ x, x ∉ Ω → isotropicDirichletGlobalValue Ω U x = 0 := by
  have hs := (mem_isotropicRealSupported_iff hΩ U.val).mp U.property
  filter_upwards [hs.2, isotropicDirichletGlobalValue_ae U] with x hx he
  intro hxo
  rw [he, hx hxo, Complex.zero_re]

/-- Actual real-valuedness identifies the complex Fourier value with the real observation. -/
theorem isotropicDirichlet_complexValue_ae {Ω : Set D} (hΩ : MeasurableSet Ω)
    (U : IsotropicDirichletState Ω) :
    ∀ᵐ x, isotropicEnergyValue 1 U.val x =
      (isotropicDirichletGlobalValue Ω U x : ℂ) := by
  have hs := (mem_isotropicRealSupported_iff hΩ U.val).mp U.property
  filter_upwards [hs.1, isotropicDirichletGlobalValue_ae U] with x him he
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using he.symm
  · simpa only [Complex.ofReal_im] using him

end PartialBalayage.Linear
