/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Tactic

/-!
# Actual dominated limits in Hilbert `L²`

A full squared-mass domination proves strong convergence along any countably generated filter.
This form applies to actual Fourier difference quotients without an assumed convergence certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PartialBalayage.Linear

/-- Full squared-mass domination gives an actual `L²` seminorm limit along a general filter. -/
theorem tendsto_eLpNorm_two_filter_of_dominated
    {X E I : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
    {l : Filter I} [l.IsCountablyGenerated] (F : I → X → E) (f b : X → E)
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) (hf : AEStronglyMeasurable f μ)
    (hb : MemLp b 2 μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x - f x‖ ≤ ‖b x‖)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Tendsto (fun i ↦ eLpNorm (F i - f) 2 μ) l (𝓝 0) := by
  have hmeas i : AEMeasurable (fun x ↦ ‖F i x - f x‖ₑ ^ (2 : ℝ)) μ :=
    ((hF i).sub hf).enorm.pow_const _
  have hbound' : ∀ᶠ i in l, (fun x ↦ ‖F i x - f x‖ₑ ^ (2 : ℝ)) ≤ᵐ[μ]
      fun x ↦ ‖b x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    exact ENNReal.rpow_le_rpow (by simpa only [enorm] using ENNReal.coe_le_coe.mpr hx)
      (by norm_num)
  have hfin : (∫⁻ x, ‖b x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ∞ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hb.eLpNorm_lt_top).ne
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ ‖F i x - f x‖ₑ ^ (2 : ℝ)) l (𝓝 0) := by
    filter_upwards [ht] with x hx
    have hz := hx.sub (tendsto_const_nhds (x := f x))
    convert (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp
      (ENNReal.tendsto_coe.mpr hz.nnnorm) using 1 <;> simp [Function.comp_def, enorm]
  have hpow : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
    simpa using tendsto_lintegral_filter_of_dominated_convergence'
      (fun x ↦ ‖b x‖ₑ ^ (2 : ℝ)) (Eventually.of_forall hmeas) hbound' hfin hlim
  have hroot := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hpow
  convert hroot using 1
  · ext i
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      ((hF i).sub hf)]
    norm_num
  · simp

/-- Squared-mass domination upgrades actual almost-everywhere convergence to an `L²` limit. -/
theorem tendsto_L2_of_ae_dominated
    {X E I : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
    {l : Filter I} [l.IsCountablyGenerated] (F : I → Lp E 2 μ) (f b : Lp E 2 μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x - f x‖ ≤ ‖b x‖)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Tendsto F l (𝓝 f) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).mpr
  exact tendsto_eLpNorm_two_filter_of_dominated (fun i ↦ F i) f b
    (fun i ↦ Lp.aestronglyMeasurable (F i)) (Lp.aestronglyMeasurable f)
    (Lp.memLp b) hbound ht

end PartialBalayage.Linear
