/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CauchyMeasureLimit
public import PartialBalayage.Linear.IntegrableL2Dense
public import PartialBalayage.Linear.FourierOperatorDefinitions

/-!
# Genuine canonical L¹ extensions of weakly bounded L² operators

Actual integrable L² approximations are dense in L¹. The weak estimate on their
differences makes their actual outputs Cauchy in measure. An almost everywhere
subsequential limit defines the extension; the same estimate proves uniqueness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace PartialBalayage.Linear

variable {X E F 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local notation "Input" => integrableL2Submodule (𝕜 := 𝕜) (E := E) (μ := μ)
local notation "InputMap" => integrableL2ToL1 (𝕜 := 𝕜) (E := E) (μ := μ)

/-- The genuine weak L¹ estimate for every actual integrable square-integrable input. -/
def HasL1WeakBound (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) : Prop :=
  ∀ u : Input, ∀ r : ℝ, 0 < r →
    μ {x | r < ‖T u.val x‖} ≤ ENNReal.ofReal ((C : ℝ) * ‖InputMap u‖ / r)

/-- A limit is witnessed by actual L¹-convergent integrable L² inputs and actual a.e. outputs. -/
def IsL1ExtensionLimit (T : Lp E 2 μ →L[𝕜] Lp F 2 μ)
    (f : Lp E 1 μ) (g : AEEqFun X F μ) : Prop :=
  ∃ u : ℕ → Input, Tendsto (fun n ↦ InputMap (u n)) atTop (𝓝 f) ∧
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ T (u n).val x) atTop (𝓝 (g x))

/-- The actual weak estimate applies to the distance between two actual operator outputs. -/
theorem operator_distance_measure_le (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : HasL1WeakBound T C) (u v : Input) {r : ℝ} (hr : 0 < r) :
    μ {x | r < dist (T u.val x) (T v.val x)} ≤
      ENNReal.ofReal ((C : ℝ) * ‖InputMap u - InputMap v‖ / r) := by
  have heq : T (u - v).val = T u.val - T v.val := T.map_sub u.val v.val
  have hs : {x | r < dist (T u.val x) (T v.val x)} =ᵐ[μ]
      {x | r < ‖T (u - v).val x‖} := by
    rw [heq]
    filter_upwards [Lp.coeFn_sub (T u.val) (T v.val)] with x hx
    simp only [hx, Pi.sub_apply, dist_eq_norm_sub]
  rw [measure_congr hs]
  simpa only [map_sub] using hb (u - v) r hr

/-- Actual L¹ convergence and the genuine weak estimate imply Cauchy convergence in measure. -/
theorem isCauchyInMeasure_operator_of_tendsto_L1
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) (hb : HasL1WeakBound T C)
    (u : ℕ → Input) {f : Lp E 1 μ}
    (hu : Tendsto (fun n ↦ InputMap (u n)) atTop (𝓝 f)) :
    IsCauchyInMeasure (μ := μ) (fun n x ↦ T (u n).val x) := by
  intro r hr δ hδ
  have hdist : Tendsto (fun p : ℕ × ℕ ↦ dist (InputMap (u p.1)) (InputMap (u p.2)))
      atTop (𝓝 0) := cauchySeq_iff_tendsto_dist_atTop_0.mp hu.cauchySeq
  have hbound : Tendsto (fun p : ℕ × ℕ ↦ ENNReal.ofReal ((C : ℝ) *
      dist (InputMap (u p.1)) (InputMap (u p.2)) / r)) atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := (C : ℝ))).mul hdist).div_const r
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbound.eventually (gt_mem_nhds hδ))
  refine ⟨max N.1 N.2, fun m hm n hn ↦ ?_⟩
  apply (operator_distance_measure_le T C hb (u m) (u n) hr).trans_lt
  simpa only [dist_eq_norm_sub] using hN (m, n)
    ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hn⟩

/-- The exact real-threshold weak coefficient passes to an actual a.e. output limit. -/
theorem weak_measure_bound_of_ae_tendsto
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) (hb : HasL1WeakBound T C)
    (u : ℕ → Input) {f : Lp E 1 μ} (g : X → F)
    (hu : Tendsto (fun n ↦ InputMap (u n)) atTop (𝓝 f))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ T (u n).val x) atTop (𝓝 (g x)))
    {r : ℝ} (hr : 0 < r) :
    μ {x | r < ‖g x‖} ≤ ENNReal.ofReal ((C : ℝ) * ‖f‖ / r) := by
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal ((C : ℝ) * ‖InputMap (u n)‖ / r))
      atTop (𝓝 (ENNReal.ofReal ((C : ℝ) * ‖f‖ / r))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul hu.norm).div_const r)
  calc
    μ {x | r < ‖g x‖} ≤ liminf (fun n ↦ μ {x | r < ‖T (u n).val x‖}) atTop :=
      measure_norm_level_le_liminf_of_ae_tendsto _ _ hg r
    _ ≤ liminf (fun n ↦ ENNReal.ofReal ((C : ℝ) * ‖InputMap (u n)‖ / r)) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n ↦ hb (u n) r hr)
    _ = _ := hlim.liminf_eq

variable [CompleteSpace F]

/-- Every actual L¹ input has an actual a.e. output limit, with no convergence premise. -/
theorem exists_L1ExtensionLimit (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : HasL1WeakBound T C) (f : Lp E 1 μ) :
    ∃ g : AEEqFun X F μ, IsL1ExtensionLimit T f g := by
  obtain ⟨u, hu⟩ := exists_integrableL2_approximation (𝕜 := 𝕜) f
  obtain ⟨ns, hns, g, hg, hlim⟩ :=
    IsCauchyInMeasure.exists_stronglyMeasurable_subsequence_limit
      (isCauchyInMeasure_operator_of_tendsto_L1 T C hb u hu)
      (fun n ↦ Lp.aestronglyMeasurable (T (u n).val))
  refine ⟨AEEqFun.mk g hg.aestronglyMeasurable, fun n ↦ u (ns n),
    hu.comp hns.tendsto_atTop, ?_⟩
  filter_upwards [hlim, AEEqFun.coeFn_mk g hg.aestronglyMeasurable] with x hx hgx
  rwa [hgx]

omit [CompleteSpace F] in
/-- The genuine weak bound forces uniqueness of the extension limit as an a.e. class. -/
theorem IsL1ExtensionLimit.unique (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : HasL1WeakBound T C) {f : Lp E 1 μ} {g h : AEEqFun X F μ}
    (hg : IsL1ExtensionLimit T f g) (hh : IsL1ExtensionLimit T f h) : g = h := by
  obtain ⟨u, hu, hug⟩ := hg
  obtain ⟨v, hv, hvh⟩ := hh
  have hinput : Tendsto (fun n ↦ InputMap (u n - v n)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using hu.sub hv
  have hout : ∀ᵐ x ∂μ, Tendsto (fun n ↦ T (u n - v n).val x)
      atTop (𝓝 (g x - h x)) := by
    have hseq : ∀ᵐ x ∂μ, ∀ n : ℕ,
        T (u n - v n).val x = T (u n).val x - T (v n).val x := by
      apply ae_all_iff.mpr
      intro n
      change (T ((u n).val - (v n).val) : X → F) =ᵐ[μ] _
      rw [map_sub]
      exact Lp.coeFn_sub _ _
    filter_upwards [hug, hvh, hseq] with x hx hy hs
    simpa only [hs] using hx.sub hy
  have hzero : (fun x ↦ g x - h x) =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_ae_tendsto_of_level_measures_tendsto_zero _ _ hout
    intro r hr
    have hlim : Tendsto (fun n ↦ ENNReal.ofReal ((C : ℝ) *
        ‖InputMap (u n - v n)‖ / r)) atTop (𝓝 0) := by
      have ht := ((tendsto_const_nhds (x := (C : ℝ))).mul hinput.norm).div_const r
      simpa only [Function.comp_def, norm_zero, mul_zero, zero_div, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ zero_le) (fun n ↦ hb (u n - v n) r hr)
  apply AEEqFun.ext
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

omit [CompleteSpace F] in
/-- Adding actual input and output approximations preserves the extension relation. -/
theorem IsL1ExtensionLimit.add (T : Lp E 2 μ →L[𝕜] Lp F 2 μ)
    {f f' : Lp E 1 μ} {g g' : AEEqFun X F μ}
    (h : IsL1ExtensionLimit T f g) (h' : IsL1ExtensionLimit T f' g') :
    IsL1ExtensionLimit T (f + f') (g + g') := by
  obtain ⟨u, hu, hug⟩ := h
  obtain ⟨v, hv, hvg⟩ := h'
  refine ⟨fun n ↦ u n + v n, by simpa only [map_add] using hu.add hv, ?_⟩
  have hseq : ∀ᵐ x ∂μ, ∀ n : ℕ,
      T (u n + v n).val x = T (u n).val x + T (v n).val x := by
    apply ae_all_iff.mpr
    intro n
    change (T ((u n).val + (v n).val) : X → F) =ᵐ[μ] _
    rw [map_add]
    exact Lp.coeFn_add _ _
  filter_upwards [hug, hvg, hseq, AEEqFun.coeFn_add g g'] with x hx hy hs hgx
  rw [hgx, Pi.add_apply]
  simpa only [hs] using hx.add hy

omit [CompleteSpace F] in
/-- Scaling actual input and output approximations preserves the extension relation. -/
theorem IsL1ExtensionLimit.smul (T : Lp E 2 μ →L[𝕜] Lp F 2 μ)
    {f : Lp E 1 μ} {g : AEEqFun X F μ} (h : IsL1ExtensionLimit T f g) (c : 𝕜) :
    IsL1ExtensionLimit T (c • f) (c • g) := by
  obtain ⟨u, hu, hug⟩ := h
  refine ⟨fun n ↦ c • u n, by simpa only [map_smul] using hu.const_smul c, ?_⟩
  have hseq : ∀ᵐ x ∂μ, ∀ n : ℕ,
      T (c • u n).val x = c • T (u n).val x := by
    apply ae_all_iff.mpr
    intro n
    change (T (c • (u n).val) : X → F) =ᵐ[μ] _
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [hug, hseq, AEEqFun.coeFn_smul c g] with x hx hs hgx
  rw [hgx, Pi.smul_apply]
  simpa only [hs] using hx.const_smul c

/-- A selected genuine output limit for every actual L¹ input. -/
def weakL1ExtensionValue (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : HasL1WeakBound T C) (f : Lp E 1 μ) : AEEqFun X F μ :=
  Classical.choose (exists_L1ExtensionLimit T C hb f)

/-- The selected actual output is witnessed by genuine approximations. -/
theorem weakL1ExtensionValue_spec (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : HasL1WeakBound T C) (f : Lp E 1 μ) :
    IsL1ExtensionLimit T f (weakL1ExtensionValue T C hb f) :=
  Classical.choose_spec (exists_L1ExtensionLimit T C hb f)

/-- The genuine canonical all-L¹ extension as an actual linear map into a.e. classes. -/
def canonicalWeakL1Extension (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : HasL1WeakBound T C) : Lp E 1 μ →ₗ[𝕜] AEEqFun X F μ where
  toFun := weakL1ExtensionValue T C hb
  map_add' f g := IsL1ExtensionLimit.unique T C hb
    (weakL1ExtensionValue_spec T C hb (f + g))
    (IsL1ExtensionLimit.add T (weakL1ExtensionValue_spec T C hb f)
      (weakL1ExtensionValue_spec T C hb g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    exact IsL1ExtensionLimit.unique T C hb (weakL1ExtensionValue_spec T C hb (c • f))
      (IsL1ExtensionLimit.smul T (weakL1ExtensionValue_spec T C hb f) c)

/-- The genuine all-L¹ linear extension keeps the exact real-threshold weak bound. -/
theorem canonicalWeakL1Extension_weak_measure_bound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) (hb : HasL1WeakBound T C)
    (f : Lp E 1 μ) {r : ℝ} (hr : 0 < r) :
    μ {x | r < ‖canonicalWeakL1Extension T C hb f x‖} ≤
      ENNReal.ofReal ((C : ℝ) * ‖f‖ / r) := by
  obtain ⟨u, hu, hg⟩ := weakL1ExtensionValue_spec T C hb f
  exact weak_measure_bound_of_ae_tendsto T C hb u _ hu hg hr

/-- The actual extension agrees with the actual L² operator on every common input class. -/
theorem canonicalWeakL1Extension_ae_eq_L2
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) (hb : HasL1WeakBound T C)
    (f : Lp E 1 μ) (u : Lp E 2 μ) (hfu : (f : X → E) =ᵐ[μ] u) :
    canonicalWeakL1Extension T C hb f =ᵐ[μ] T u := by
  have hu : Integrable (u : X → E) μ := (L1.integrable_coeFn f).congr hfu
  let v : Input := ⟨u, hu⟩
  have hinput : InputMap v = f := by
    apply Lp.ext
    exact (integrableL2ToL1_ae v).trans hfu.symm
  have hconstant : IsL1ExtensionLimit T f (T u : AEEqFun X F μ) := by
    refine ⟨fun _ ↦ v, ?_, Eventually.of_forall fun _ ↦ tendsto_const_nhds⟩
    simpa only [hinput] using (tendsto_const_nhds (x := f) : Tendsto _ atTop _)
  have heq := IsL1ExtensionLimit.unique T C hb
    (weakL1ExtensionValue_spec T C hb f) hconstant
  change weakL1ExtensionValue T C hb f =ᵐ[μ] (T u : X → F)
  rw [heq]

/-- The actual all-L¹ extension retains its exact weak bound at every extended-real threshold. -/
theorem canonicalWeakL1Extension_level_bound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) (hb : HasL1WeakBound T C)
    (f : Lp E 1 μ) (α : ℝ≥0∞) :
    α * μ {x | α < ‖canonicalWeakL1Extension T C hb f x‖ₑ} ≤
      (C : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  by_cases hzero : α = 0
  · simp [hzero]
  by_cases htop : α = ⊤
  · simp [htop]
  let r := α.toReal
  have hr : 0 < r := ENNReal.toReal_pos hzero htop
  have hα : ENNReal.ofReal r = α := ENNReal.ofReal_toReal htop
  have hset : {x | α < ‖canonicalWeakL1Extension T C hb f x‖ₑ} =
      {x | r < ‖canonicalWeakL1Extension T C hb f x‖} := by
    ext x
    change α < ‖canonicalWeakL1Extension T C hb f x‖ₑ ↔
      r < ‖canonicalWeakL1Extension T C hb f x‖
    rw [← hα, ← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le
  have hmass : ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [ofReal_norm, Lp.enorm_def,
      eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  rw [hset, ← hα]
  calc
    ENNReal.ofReal r * μ {x | r < ‖canonicalWeakL1Extension T C hb f x‖} ≤
        ENNReal.ofReal r * ENNReal.ofReal ((C : ℝ) * ‖f‖ / r) :=
      mul_le_mul_right (canonicalWeakL1Extension_weak_measure_bound T C hb f hr) _
    _ = ENNReal.ofReal ((C : ℝ) * ‖f‖) := by
      rw [← ENNReal.ofReal_mul hr.le]
      congr 1
      field_simp
    _ = (C : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ ∂μ := by
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, hmass]

/-- Actual L² weak bounds supply the independent full-L¹ linear weak-type predicate. -/
theorem isLinearWeakTypeBound_of_HasL1WeakBound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) (hb : HasL1WeakBound T C) :
    IsLinearWeakTypeBound (𝕜 := 𝕜) T (C : ℝ≥0∞) :=
  ⟨canonicalWeakL1Extension T C hb, canonicalWeakL1Extension_ae_eq_L2 T C hb,
    canonicalWeakL1Extension_level_bound T C hb⟩

omit [CompleteSpace F] in
/-- Convert the actual every-level L² weak estimate to the finite real-threshold form. -/
theorem hasL1WeakBound_of_level_bound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : ∀ u : Lp E 2 μ, Integrable (u : X → E) μ → ∀ α : ℝ≥0∞,
      α * μ {x | α < ‖T u x‖ₑ} ≤ (C : ℝ≥0∞) * ∫⁻ x, ‖u x‖ₑ ∂μ) :
    HasL1WeakBound T C := by
  intro u r hr
  have hset : {x | ENNReal.ofReal r < ‖T u.val x‖ₑ} = {x | r < ‖T u.val x‖} := by
    ext x
    change ENNReal.ofReal r < ‖T u.val x‖ₑ ↔ r < ‖T u.val x‖
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le
  have hmass : ENNReal.ofReal ‖InputMap u‖ = ∫⁻ x, ‖u.val x‖ₑ ∂μ := by
    rw [ofReal_norm]
    exact u.property.enorm_toL1
  have h := hb u.val u.property (ENNReal.ofReal r)
  rw [hset, ← hmass] at h
  calc
    μ {x | r < ‖T u.val x‖} ≤
        ((C : ℝ≥0∞) * ENNReal.ofReal ‖InputMap u‖) / ENNReal.ofReal r := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
        (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using h
    _ = ENNReal.ofReal ((C : ℝ) * ‖InputMap u‖ / r) := by
      rw [ENNReal.ofReal_div_of_pos hr, ENNReal.ofReal_mul C.coe_nonneg,
        ENNReal.ofReal_coe_nnreal]

/-- The genuine all-L¹ extension follows directly from an actual L¹ and L² weak bound. -/
theorem isLinearWeakTypeBound_of_L2_level_bound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0)
    (hb : ∀ u : Lp E 2 μ, Integrable (u : X → E) μ → ∀ α : ℝ≥0∞,
      α * μ {x | α < ‖T u x‖ₑ} ≤ (C : ℝ≥0∞) * ∫⁻ x, ‖u x‖ₑ ∂μ) :
    IsLinearWeakTypeBound (𝕜 := 𝕜) T (C : ℝ≥0∞) :=
  isLinearWeakTypeBound_of_HasL1WeakBound T C (hasL1WeakBound_of_level_bound T C hb)

/-- For a finite coefficient, the full-L¹ predicate is equivalent to the actual L¹ and L² bound. -/
theorem isLinearWeakTypeBound_iff_L2_level_bound
    (T : Lp E 2 μ →L[𝕜] Lp F 2 μ) (C : ℝ≥0) :
    IsLinearWeakTypeBound (𝕜 := 𝕜) T (C : ℝ≥0∞) ↔
      ∀ u : Lp E 2 μ, Integrable (u : X → E) μ → ∀ α : ℝ≥0∞,
        α * μ {x | α < ‖T u x‖ₑ} ≤ (C : ℝ≥0∞) * ∫⁻ x, ‖u x‖ₑ ∂μ := by
  constructor
  · rintro ⟨S, hS, hbound⟩ u hu α
    let f := hu.toL1 u
    have hfu : (f : X → E) =ᵐ[μ] u := hu.coeFn_toL1
    have houtput := hS f u hfu
    have hset : {x | α < ‖S f x‖ₑ} =ᵐ[μ] {x | α < ‖T u x‖ₑ} := by
      filter_upwards [houtput] with x hx
      simp only [hx]
    have hmass : (∫⁻ x, ‖f x‖ₑ ∂μ) = ∫⁻ x, ‖u x‖ₑ ∂μ :=
      lintegral_congr_ae (hfu.fun_comp enorm)
    rw [← measure_congr hset, ← hmass]
    exact hbound f α
  · exact isLinearWeakTypeBound_of_L2_level_bound T C

end PartialBalayage.Linear
