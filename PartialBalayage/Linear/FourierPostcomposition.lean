/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fourier transforms commute with constant linear maps on the output

The Schwartz identity follows from the Bochner integral. Density then extends it to the actual
unitary Fourier transform on `L²`. This permits taking traces and constant tensor components of
Fourier multipliers in physical space.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform

namespace PartialBalayage.Linear

variable {X E F : Type*}
variable [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
variable [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A constant continuous linear map commutes with the Schwartz Fourier transform. -/
theorem fourier_postcomp_schwartz (L : E →L[ℂ] F) (f : SchwartzMap X E) :
    𝓕 (f.postcompCLM L) = (𝓕 f).postcompCLM L := by
  ext ξ
  change (∫ x : X, Real.fourierChar (-inner ℝ x ξ) • L (f x)) =
    L (∫ x : X, Real.fourierChar (-inner ℝ x ξ) • f x)
  simp_rw [Circle.smul_def, ← map_smul]
  apply L.integral_comp_comm
  exact (Real.fourierIntegral_convergent_iff ξ).mpr f.integrable

omit [CompleteSpace E] [CompleteSpace F] in
/-- Postcomposition in `L²` agrees with postcomposition of its dense Schwartz representatives. -/
theorem compLp_toLp_schwartz (L : E →L[ℂ] F) (f : SchwartzMap X E) :
    L.compLp (f.toLp 2) = (f.postcompCLM L).toLp 2 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (f.toLp 2), f.coeFn_toLp 2,
    (f.postcompCLM L).coeFn_toLp 2] with x hL hf hg
  rw [hL, hf, hg]
  rfl

/-- Constant output maps commute with the genuine unitary `L²` Fourier transform. -/
theorem fourier_compLp (L : E →L[ℂ] F) (f : Lp E 2 (volume : Measure X)) :
    𝓕 (L.compLp f) = L.compLp (𝓕 f) := by
  apply DenseRange.induction_on
    (p := fun g : Lp E 2 (volume : Measure X) ↦ 𝓕 (L.compLp g) = L.compLp (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((fourierCLM ℂ (Lp F 2 volume)).comp (L.compLpL 2 volume)).continuous
      ((L.compLpL 2 volume).comp (fourierCLM ℂ (Lp E 2 volume))).continuous
  intro g
  simp only [SchwartzMap.toLpCLM_apply, compLp_toLp_schwartz,
    SchwartzMap.toLp_fourier_eq, fourier_postcomp_schwartz]

/-- The inverse Fourier transform also commutes with constant output maps. -/
theorem fourierInv_compLp (L : E →L[ℂ] F) (f : Lp E 2 (volume : Measure X)) :
    𝓕⁻ (L.compLp f) = L.compLp (𝓕⁻ f) := by
  apply (Lp.fourierTransformₗᵢ X F).injective
  change 𝓕 (𝓕⁻ (L.compLp f)) = 𝓕 (L.compLp (𝓕⁻ f))
  rw [fourier_fourierInv_eq, fourier_compLp, fourier_fourierInv_eq]

end PartialBalayage.Linear
