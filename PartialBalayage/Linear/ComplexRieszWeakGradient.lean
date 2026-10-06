/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonSelfEnergy
public import PartialBalayage.Linear.RieszWeakGradient
public import PartialBalayage.Linear.HessianDerivative

/-!
# The full complex Riesz vector represents the actual physical gradient

The complex physical Poisson equation gives the full norm-weighted Fourier identity.
Each genuine Riesz coordinate is consequently a represented distributional derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set Filter LineDeriv TemperedDistribution
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal SchwartzMap LineDeriv

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)

/-- The genuine Riesz Fourier coordinate equals the actual derivative frequency weight. -/
theorem complex_fourier_rieszCoordinate_eq_first_weight_ae (u q : L²ℂ)
    (hFrequency : ∀ᵐ ξ, (‖ξ‖ : ℂ) • (𝓕 u : L²ℂ) ξ =
      (2 * Real.pi : ℂ)⁻¹ • (𝓕 q : L²ℂ) ξ) (i : Fin n) :
    (𝓕 ((projectionCoordinateCLM i).compLp (rieszL2 q)) : L²ℂ) =ᵐ[volume]
      fun ξ ↦ ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) * (𝓕 u : L²ℂ) ξ := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
  filter_upwards [fourier_rieszCoordinate_ae q i, hFrequency] with ξ hr hn
  rw [hr]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hnorm : (‖ξ‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
    have hq : (𝓕 q : L²ℂ) ξ =
        (2 * Real.pi : ℂ) * ((‖ξ‖ : ℂ) * (𝓕 u : L²ℂ) ξ) := by
      have h := congrArg (fun z : ℂ ↦ (2 * Real.pi : ℂ) * z) hn
      simp only [smul_eq_mul, mul_inv_cancel_left₀ hπ] at h
      exact h.symm
    rw [hq]
    field_simp [hnorm]

/-- The true coordinate first-derivative symbol has temperate growth. -/
theorem hasTemperateGrowth_firstDerivativeSymbol (i : Fin n) :
    (fun ξ : D ↦ (2 * Real.pi * Complex.I) * (ξ i : ℂ)).HasTemperateGrowth := by
  have hc : (fun ξ : D ↦ (ξ i : ℂ)).HasTemperateGrowth := by
    simpa [EuclideanSpace.inner_single_right] using
      (show (fun ξ : D ↦ (inner ℝ ξ
        (EuclideanSpace.single i (1 : ℝ)) : ℂ)).HasTemperateGrowth by fun_prop)
  exact (show (fun _ : D ↦ (2 * Real.pi * Complex.I)).HasTemperateGrowth
    by fun_prop).mul hc

/-- Fourier transformation of the actual first derivative has its exact symbol. -/
theorem complex_fourier_first_derivative_eq (u : L²ℂ) (i : Fin n) :
    𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(D, ℂ))) =
      smulLeftCLM ℂ (fun ξ : D ↦ (2 * Real.pi * Complex.I) * (ξ i : ℂ))
        ((𝓕 u : L²ℂ) : 𝓢'(D, ℂ)) := by
  rw [TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq]
  have hw : (fun ξ : D ↦ (inner ℝ ξ
      (EuclideanSpace.single i (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
  have hs := congrArg (fun L : 𝓢'(D, ℂ) →L[ℂ] 𝓢'(D, ℂ) ↦
    L ((𝓕 u : L²ℂ) : 𝓢'(D, ℂ)))
      (smulLeftCLM_smul (F := ℂ) hw (2 * Real.pi * Complex.I))
  simp only [smul_apply] at hs
  rw [← hs]
  have hsymbol : (2 * Real.pi * Complex.I) •
      (fun ξ : D ↦ (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) =
      (fun ξ : D ↦ (2 * Real.pi * Complex.I) * (ξ i : ℂ)) := by
    ext ξ
    simp only [Pi.smul_apply, smul_eq_mul, EuclideanSpace.inner_single_right,
      one_mul, starRingEnd_apply, star_trivial]
  exact congrArg (fun w : D → ℂ ↦ smulLeftCLM ℂ w ((𝓕 u : L²ℂ) : 𝓢'(D, ℂ))) hsymbol

/-- Every actual complex Riesz coordinate represents a genuine physical first derivative. -/
theorem complex_rieszCoordinate_represents_first_derivative (u q : L²ℂ)
    (hPDE : ∀ W : H01 (univ : Set D),
      inner ℂ u (h01PoissonGenerator W) = inner ℂ q (h01ComplexValueCLM W)) (i : Fin n) :
    ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(D, ℂ)) =
      ((projectionCoordinateCLM i).compLp (rieszL2 q) : 𝓢'(D, ℂ)) := by
  have h := tempered_smulLeftCLM_eq_of_ae_mul (𝓕 u)
    (𝓕 ((projectionCoordinateCLM i).compLp (rieszL2 q)))
    (hasTemperateGrowth_firstDerivativeSymbol i)
    (complex_fourier_rieszCoordinate_eq_first_weight_ae u q
      (complex_isotropicNormFourier_ae_of_h01_equation u q hPDE) i)
  rw [← Lp.fourier_toTemperedDistribution_eq, ← complex_fourier_first_derivative_eq] at h
  have hinv := congrArg (fun T : 𝓢'(D, ℂ) ↦ 𝓕⁻ T) h
  simpa only [fourierInv_fourier_eq] using hinv.symm

end PartialBalayage.Linear
