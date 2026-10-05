/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.HessianMultiplier
public import PartialBalayage.Linear.FourierPostcomposition
public import PartialBalayage.Linear.LocalSecondSobolev

/-!
# Actual Hessian derivatives of an L² Laplace solution

The full Frobenius-valued Fourier operator of the Laplace forcing is identified with the
represented distributional second derivatives of the state. The equation itself supplies
order-two Sobolev regularity; no second-derivative representation is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv

namespace PartialBalayage.Linear

variable {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure X)

/-- A represented temperate multiplication equation determines the actual pointwise product.
Local integrability suffices, so no integrability of the polynomial symbol is assumed. -/
theorem ae_eq_mul_of_tempered_smulLeftCLM (a b : L²) {w : X → ℂ}
    (hw : w.HasTemperateGrowth)
    (heq : (b : 𝓢'(X, ℂ)) = smulLeftCLM ℂ w (a : 𝓢'(X, ℂ))) :
    b =ᵐ[volume] fun x ↦ w x * a x := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp b).locallyIntegrable (by norm_num))
    ((Lp.memLp a).locallyIntegrable (by norm_num) |>.continuous_mul hw.1.continuous)
  intro φ hφ hφs
  let ψ : 𝓢(X, ℂ) := (hφs.comp_left Complex.ofRealCLM.map_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have h := congrArg (fun T : 𝓢'(X, ℂ) ↦ T ψ) heq
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hw, smul_eq_mul] at h
  convert h using 1 <;> apply integral_congr_ae <;> filter_upwards with x
  · change φ x • (b x : ℂ) = (φ x : ℂ) * b x
    exact Complex.real_smul
  · change φ x • (w x * a x) = (w x * (φ x : ℂ)) * a x
    rw [Complex.real_smul]
    ring

/-- An actual almost-everywhere multiplication identity gives its tempered-distribution
equation even when the symbol itself has polynomial growth. -/
theorem tempered_smulLeftCLM_eq_of_ae_mul (a b : L²) {w : X → ℂ}
    (hw : w.HasTemperateGrowth) (heq : b =ᵐ[volume] fun x ↦ w x * a x) :
    (b : 𝓢'(X, ℂ)) = smulLeftCLM ℂ w (a : 𝓢'(X, ℂ)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hw, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]
  ring

/-- The actual Fourier representatives obey the Laplace frequency equation. -/
theorem fourier_eq_laplace_weight_ae (u q : L²)
    (hΔ : Δ (u : 𝓢'(X, ℂ)) = -(q : 𝓢'(X, ℂ))) :
    (𝓕 q : L²) =ᵐ[volume] fun ξ ↦
      ((2 * Real.pi : ℂ) ^ (2 : ℕ) * (‖ξ‖ : ℂ) ^ (2 : ℕ)) * (𝓕 u : L²) ξ := by
  have h := congrArg (fun T : 𝓢'(X, ℂ) ↦ 𝓕 T) hΔ
  have hLap : Δ (u : 𝓢'(X, ℂ)) = ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ) •
      fourierMultiplierCLM ℂ (fun ξ : X ↦ (‖ξ‖ ^ (2 : ℕ) : ℝ)) (u : 𝓢'(X, ℂ)) := by
    simpa only [Complex.coe_smul] using laplacian_eq_fourierMultiplierCLM (u : 𝓢'(X, ℂ))
  rw [hLap] at h
  simp only [fourier_smul, fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    Lp.fourier_toTemperedDistribution_eq] at h
  rw [FourierTransform.fourier_neg (q : 𝓢'(X, ℂ)),
    Lp.fourier_toTemperedDistribution_eq] at h
  have hpos : ((2 * Real.pi) ^ 2 : ℂ) •
      smulLeftCLM ℂ (fun ξ : X ↦ ((‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ))
        ((𝓕 u : L²) : 𝓢'(X, ℂ)) = ((𝓕 q : L²) : 𝓢'(X, ℂ)) := by
    apply neg_injective
    convert h using 1
    ext φ
    change -(((2 * Real.pi) ^ 2 : ℂ) * _) = ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ) * _
    push_cast
    ring
  have heq : ((𝓕 q : L²) : 𝓢'(X, ℂ)) = smulLeftCLM ℂ
      (fun ξ : X ↦ ((2 * Real.pi) ^ (2 : ℕ) : ℂ) * ((‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ))
        ((𝓕 u : L²) : 𝓢'(X, ℂ)) := by
    rw [← hpos]
    have hs := congrArg (fun L : 𝓢'(X, ℂ) →L[ℂ] 𝓢'(X, ℂ) ↦
      L ((𝓕 u : L²) : 𝓢'(X, ℂ)))
      (smulLeftCLM_smul (F := ℂ)
        (show (fun ξ : X ↦ ((‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ)).HasTemperateGrowth by fun_prop)
        (((2 * Real.pi) ^ 2 : ℂ)))
    have hsymbol : (((2 * Real.pi) ^ 2 : ℂ) •
        (fun ξ : X ↦ ((‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ))) =
        (fun ξ : X ↦ ((2 * Real.pi) ^ 2 : ℂ) * ((‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ)) := by
      ext ξ
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsymbol] at hs
    exact hs.symm
  simpa only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    ae_eq_mul_of_tempered_smulLeftCLM (𝓕 u) (𝓕 q) (by fun_prop) heq

/-- A Hessian matrix entry is a genuine scalar continuous linear projection. -/
def hessianEntryCLM (i j : Fin d) : EuclideanSpace ℂ (Fin d × Fin d) →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : Fin d × Fin d ↦ ℂ) (i, j)

/-- The Fourier transform of an actual Hessian entry is its exact normalized symbol. -/
theorem fourier_hessianEntry_ae (q : L²) (i j : Fin d) :
    (𝓕 ((hessianEntryCLM i j).compLp (hessianL2 q)) : L²) =ᵐ[volume]
      fun ξ ↦ (𝓕 q : L²) ξ *
        (-(ξ i : ℂ) * (ξ j : ℂ) / (‖ξ‖ : ℂ) ^ (2 : ℕ)) := by
  rw [fourier_compLp]
  have hF : (𝓕 (hessianL2 q) :
      Lp (EuclideanSpace ℂ (Fin d × Fin d)) 2 (volume : Measure X)) =
      multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 q) := by
    change 𝓕 (𝓕⁻ (multiplyVectorL2 hessianSymbol measurable_hessianSymbol
      norm_hessianSymbol_le (𝓕 q))) = _
    exact fourier_fourierInv_eq _
  rw [hF]
  filter_upwards [(hessianEntryCLM i j).coeFn_compLp
    (multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 q)),
    (vectorSymbol_memLp hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le
      (𝓕 q)).coeFn_toLp] with ξ hentry hm
  rw [hentry]
  change hessianEntryCLM i j
    (((vectorSymbol_memLp hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le
      (𝓕 q)).toLp _) ξ) = _
  rw [hm, map_smul]
  change (𝓕 q : L²) ξ * hessianSymbol ξ (i, j) = _
  rw [hessianSymbol_apply]

/-- The actual Hessian entry of a Laplace forcing has the second-derivative frequency symbol. -/
theorem fourier_hessianEntry_eq_second_weight_ae (u q : L²)
    (hΔ : Δ (u : 𝓢'(X, ℂ)) = -(q : 𝓢'(X, ℂ))) (i j : Fin d) :
    (𝓕 ((hessianEntryCLM i j).compLp (hessianL2 q)) : L²) =ᵐ[volume]
      fun ξ ↦ (-((2 * Real.pi : ℂ) ^ (2 : ℕ)) * (ξ i : ℂ) * (ξ j : ℂ)) *
        (𝓕 u : L²) ξ := by
  filter_upwards [fourier_hessianEntry_ae q i j, fourier_eq_laplace_weight_ae u q hΔ]
    with ξ hh hq
  rw [hh, hq]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hn : (‖ξ‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hξ
    field_simp

/-- Coordinate second-derivative symbols are genuine temperate functions. -/
theorem hasTemperateGrowth_secondDerivativeSymbol (i j : Fin d) :
    (fun ξ : X ↦ -((2 * Real.pi : ℂ) ^ (2 : ℕ)) * (ξ i : ℂ) *
      (ξ j : ℂ)).HasTemperateGrowth := by
  have hc (k : Fin d) : (fun ξ : X ↦ (ξ k : ℂ)).HasTemperateGrowth := by
    simpa [EuclideanSpace.inner_single_right] using
      (show (fun ξ : X ↦ (inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℂ)).HasTemperateGrowth
        by fun_prop)
  exact ((show (fun _ : X ↦ -((2 * Real.pi : ℂ) ^ (2 : ℕ))).HasTemperateGrowth
    by fun_prop).mul (hc i)).mul (hc j)

/-- Fourier transformation of the true iterated derivative has its exact polynomial symbol. -/
theorem fourier_second_derivative_eq (u : L²) (i j : Fin d) :
    𝓕 (∂_{EuclideanSpace.single j (1 : ℝ)}
      (∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(X, ℂ)))) =
        smulLeftCLM ℂ
          (fun ξ : X ↦ -((2 * Real.pi : ℂ) ^ (2 : ℕ)) * (ξ i : ℂ) * (ξ j : ℂ))
          ((𝓕 u : L²) : 𝓢'(X, ℂ)) := by
  rw [TemperedDistribution.fourier_lineDerivOp_eq,
    TemperedDistribution.fourier_lineDerivOp_eq, map_smul, smul_smul,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop),
    Lp.fourier_toTemperedDistribution_eq]
  have hw : ((fun ξ : X ↦ (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) *
      (fun ξ : X ↦ (inner ℝ ξ (EuclideanSpace.single j (1 : ℝ)) : ℂ))).HasTemperateGrowth :=
    by fun_prop
  have hs := congrArg (fun L : 𝓢'(X, ℂ) →L[ℂ] 𝓢'(X, ℂ) ↦
    L ((𝓕 u : L²) : 𝓢'(X, ℂ)))
      (smulLeftCLM_smul (F := ℂ) hw ((2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I)))
  simp only [smul_apply] at hs
  rw [← hs]
  have hsymbol : ((2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I)) •
      ((fun ξ : X ↦ (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) *
        (fun ξ : X ↦ (inner ℝ ξ (EuclideanSpace.single j (1 : ℝ)) : ℂ))) =
      (fun ξ : X ↦ -((2 * Real.pi : ℂ) ^ (2 : ℕ)) * (ξ i : ℂ) * (ξ j : ℂ)) := by
    ext ξ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial]
    ring_nf
    simp
  exact congrArg (fun w : X → ℂ ↦ smulLeftCLM ℂ w ((𝓕 u : L²) : 𝓢'(X, ℂ))) hsymbol

/-- Every genuine Hessian entry is the represented second derivative of the actual state. -/
theorem hessianEntry_represents_second_derivative (u q : L²)
    (hΔ : Δ (u : 𝓢'(X, ℂ)) = -(q : 𝓢'(X, ℂ))) (i j : Fin d) :
    ∂_{EuclideanSpace.single j (1 : ℝ)}
      (∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(X, ℂ))) =
        ((hessianEntryCLM i j).compLp (hessianL2 q) : 𝓢'(X, ℂ)) := by
  have h := tempered_smulLeftCLM_eq_of_ae_mul (𝓕 u)
    (𝓕 ((hessianEntryCLM i j).compLp (hessianL2 q)))
    (hasTemperateGrowth_secondDerivativeSymbol i j)
    (fourier_hessianEntry_eq_second_weight_ae u q hΔ i j)
  rw [← Lp.fourier_toTemperedDistribution_eq, ← fourier_second_derivative_eq] at h
  have hinv := congrArg (fun T : 𝓢'(X, ℂ) ↦ 𝓕⁻ T) h
  simpa only [fourierInv_fourier_eq] using hinv.symm

end PartialBalayage.Linear
