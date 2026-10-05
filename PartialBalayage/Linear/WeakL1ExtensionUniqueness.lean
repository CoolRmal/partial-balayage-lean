/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WeakL1Extension

/-!
# Uniqueness of the genuine full-L¹ extension

The weak estimate itself proves continuity from L¹ norm convergence to convergence
in measure. Thus every weakly bounded linear all-L¹ extension agrees with the actual
canonical extension; no continuity or approximation certificate is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace PartialBalayage.Linear

variable {X E F 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The every-level weak estimate for a genuine all-L¹ map implies its real-threshold bound. -/
theorem linearMap_weak_measure_bound_of_level_bound
    (S : Lp E 1 μ →ₗ[𝕜] AEEqFun X F μ) (D : ℝ≥0)
    (hb : ∀ (f : Lp E 1 μ) (α : ℝ≥0∞),
      α * μ {x | α < ‖S f x‖ₑ} ≤ (D : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ ∂μ)
    (f : Lp E 1 μ) {r : ℝ} (hr : 0 < r) :
    μ {x | r < ‖S f x‖} ≤ ENNReal.ofReal ((D : ℝ) * ‖f‖ / r) := by
  have hset : {x | ENNReal.ofReal r < ‖S f x‖ₑ} = {x | r < ‖S f x‖} := by
    ext x
    change ENNReal.ofReal r < ‖S f x‖ₑ ↔ r < ‖S f x‖
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le
  have hmass : ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [ofReal_norm, Lp.enorm_def,
      eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  have h := hb f (ENNReal.ofReal r)
  rw [hset, ← hmass] at h
  calc
    μ {x | r < ‖S f x‖} ≤
        ((D : ℝ≥0∞) * ENNReal.ofReal ‖f‖) / ENNReal.ofReal r := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
        (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using h
    _ = ENNReal.ofReal ((D : ℝ) * ‖f‖ / r) := by
      rw [ENNReal.ofReal_div_of_pos hr, ENNReal.ofReal_mul D.coe_nonneg,
        ENNReal.ofReal_coe_nnreal]

/-- A genuine weakly bounded linear map is continuous from L¹ to convergence in measure. -/
theorem linearMap_tendstoInMeasure_of_weak_bound
    (S : Lp E 1 μ →ₗ[𝕜] AEEqFun X F μ) (D : ℝ≥0)
    (hb : ∀ (f : Lp E 1 μ) (r : ℝ), 0 < r →
      μ {x | r < ‖S f x‖} ≤ ENNReal.ofReal ((D : ℝ) * ‖f‖ / r))
    (u : ℕ → Lp E 1 μ) {f : Lp E 1 μ} (hu : Tendsto u atTop (𝓝 f)) :
    TendstoInMeasure μ (fun n x ↦ S (u n) x) atTop (S f) := by
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have hdiff : Tendsto (fun n ↦ u n - f) atTop (𝓝 0) := by
    simpa only [sub_self] using hu.sub (tendsto_const_nhds (x := f))
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal ((D : ℝ) * ‖u n - f‖ / (ε / 2)))
      atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := (D : ℝ))).mul hdiff.norm).div_const (ε / 2)
    simpa only [Function.comp_def, norm_zero, mul_zero, zero_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le)
  intro n
  have hclass : S (u n - f) = S (u n) - S f := S.map_sub _ _
  have hsub : {x | ε ≤ ‖S (u n) x - S f x‖} ≤ᵐ[μ]
      {x | ε / 2 < ‖S (u n - f) x‖} := by
    rw [hclass]
    filter_upwards [AEEqFun.coeFn_sub (S (u n)) (S f)] with x hx
    intro hmem
    change ε ≤ ‖S (u n) x - S f x‖ at hmem
    rw [hx, Pi.sub_apply]
    linarith
  exact (measure_mono_ae hsub).trans (hb (u n - f) (ε / 2) (by linarith))

variable [CompleteSpace F]

/-- Any genuine weakly bounded all-L¹ extension is the actual canonical extension. -/
theorem canonicalWeakL1Extension_unique
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) (hT : HasL1WeakBound T C)
    (S : Lp E 1 μ →ₗ[𝕜] AEEqFun X F μ) (D : ℝ≥0)
    (hagree : ∀ (f : Lp E 1 μ) (u : Lp E 2 μ), (f : X → E) =ᵐ[μ] u →
      (S f : X → F) =ᵐ[μ] T u)
    (hbound : ∀ (f : Lp E 1 μ) (α : ℝ≥0∞),
      α * μ {x | α < ‖S f x‖ₑ} ≤ (D : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ ∂μ) :
    S = canonicalWeakL1Extension T C hT := by
  apply LinearMap.ext
  intro f
  obtain ⟨u, hu⟩ := exists_integrableL2_approximation (𝕜 := 𝕜) f
  have hmeasure := linearMap_tendstoInMeasure_of_weak_bound S D
    (fun f r hr ↦ linearMap_weak_measure_bound_of_level_bound S D hbound f hr)
    (fun n ↦ integrableL2ToL1 (u n)) hu
  obtain ⟨ns, hns, hlim⟩ := hmeasure.exists_seq_tendsto_ae
  have hseq : ∀ᵐ x ∂μ, ∀ n : ℕ,
      S (integrableL2ToL1 (u (ns n))) x = T (u (ns n)).val x := by
    apply ae_all_iff.mpr
    intro n
    exact hagree _ _ (integrableL2ToL1_ae _)
  have hactual : IsL1ExtensionLimit T f (S f) := by
    refine ⟨fun n ↦ u (ns n), hu.comp hns.tendsto_atTop, ?_⟩
    filter_upwards [hlim, hseq] with x hx hs
    simpa only [hs] using hx
  exact IsL1ExtensionLimit.unique T C hT hactual (weakL1ExtensionValue_spec T C hT f)

/-- The genuine canonical operator is independent of the selected finite weak coefficient. -/
theorem canonicalWeakL1Extension_independent_bound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C D : ℝ≥0)
    (hC : HasL1WeakBound T C) (hD : HasL1WeakBound T D) :
    canonicalWeakL1Extension T C hC = canonicalWeakL1Extension T D hD := by
  apply LinearMap.ext
  intro f
  exact IsL1ExtensionLimit.unique T C hC (weakL1ExtensionValue_spec T C hC f)
    (weakL1ExtensionValue_spec T D hD f)

end PartialBalayage.Linear
