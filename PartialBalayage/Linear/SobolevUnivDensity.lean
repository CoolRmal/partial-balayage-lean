/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CompactSobolevDensity
public import PartialBalayage.Linear.SobolevSpatialCutoff
public import CenteredMaximal.Ball.LocalWeakPairing
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Genuine whole-space Dirichlet density

Smooth expanding cutoffs converge in the actual value-gradient norm. Each cutoff weak graph
has compact value support and hence belongs to the genuine compact-test closure. Closing this
sequence proves that every whole-space weak first-derivative graph belongs to `H01`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter ENNReal
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace Topology ENNReal

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- Dominated convergence in actual `L²`, stated for measurable representatives. -/
theorem tendsto_eLpNorm_two_of_dominated
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ} {f b : α → ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ) (hf : AEStronglyMeasurable f μ)
    (hb : MemLp b 2 μ) (hbound : ∀ k, ∀ᵐ x ∂μ, ‖F k x - f x‖ ≤ ‖b x‖)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun k ↦ F k x) atTop (𝓝 (f x))) :
    Tendsto (fun k ↦ eLpNorm (F k - f) 2 μ) atTop (𝓝 0) := by
  have hmeas k : AEMeasurable (fun x ↦ ‖F k x - f x‖ₑ ^ (2 : ℝ)) μ :=
    ((hF k).sub hf).enorm.pow_const _
  have hbound' k : (fun x ↦ ‖F k x - f x‖ₑ ^ (2 : ℝ)) ≤ᵐ[μ]
      fun x ↦ ‖b x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hbound k] with x hx
    exact ENNReal.rpow_le_rpow (by simpa only [enorm] using ENNReal.coe_le_coe.mpr hx)
      (by norm_num)
  have hfin : (∫⁻ x, ‖b x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ∞ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hb.eLpNorm_lt_top).ne
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k ↦ ‖F k x - f x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    filter_upwards [ht] with x hx
    have hz : Tendsto (fun k ↦ F k x - f x) atTop (𝓝 (f x - f x)) :=
      hx.sub tendsto_const_nhds
    convert (continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp
      (tendsto_coe.mpr hz.nnnorm) using 1 <;> simp [Function.comp_def, enorm]
  have hpow : Tendsto (fun k ↦ ∫⁻ x, ‖F k x - f x‖ₑ ^ (2 : ℝ) ∂μ)
      atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence' (fun x ↦ ‖b x‖ₑ ^ (2 : ℝ))
      hmeas hbound' hfin hlim
  have hroot := (continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hpow
  convert hroot using 1
  · ext k
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      ((hF k).sub hf)]
    norm_num
  · simp

private def densityScale (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

private theorem densityScale_pos (k : ℕ) : 0 < densityScale k := by
  unfold densityScale
  positivity

private theorem densityScale_le_one (k : ℕ) : densityScale k ≤ 1 := by
  unfold densityScale
  exact inv_le_one_of_one_le₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) k])

private theorem densityScale_tendsto : Tendsto densityScale atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

private def densityBase : EuclideanSpace ℝ (Fin d) → ℝ :=
  CenteredMaximal.Ball.smoothBallCutoff d 0 1 1

private theorem densityBase_test : IsTestFn univ (densityBase (d := d)) :=
  ⟨CenteredMaximal.Ball.smoothBallCutoff_contDiff_smooth d 0 1 1,
    CenteredMaximal.Ball.smoothBallCutoff_hasCompactSupport d 0 (by norm_num) (by norm_num),
    subset_univ _⟩

private def densityCutoff (k : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  densityBase (densityScale k • x)

private theorem densityCutoff_test (k : ℕ) :
    IsTestFn univ (densityCutoff (d := d) k) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin d) ↦ densityScale k • x) := by fun_prop
  refine ⟨densityBase_test.1.comp hs,
    densityBase_test.2.1.comp_smul (densityScale_pos k).ne', subset_univ _⟩

private theorem densityCutoff_norm (k : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖densityCutoff k x‖ ≤ 1 :=
  CenteredMaximal.Ball.smoothBallCutoff_norm_le_one d 0 1 1 _

private theorem densityCutoff_partial (k : ℕ) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (densityCutoff k) x =
      densityScale k * partialD i densityBase (densityScale k • x) := by
  have hc := (densityBase_test.1.differentiable (by simp) (densityScale k • x)).hasFDerivAt.comp
    x ((hasFDerivAt_id x).const_smul (densityScale k))
  change (fderiv ℝ (densityBase ∘ (fun z ↦ densityScale k • z)) x)
    (EuclideanSpace.single i (1 : ℝ)) = _
  rw [hc.fderiv, ContinuousLinearMap.comp_apply]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul, partialD]

private theorem densityCutoff_tendsto (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun k ↦ densityCutoff k x) atTop (𝓝 1) := by
  have ht := densityBase_test.continuous.continuousAt.tendsto.comp
    (densityScale_tendsto.smul_const x)
  have hzero : densityBase (d := d) 0 = 1 :=
    CenteredMaximal.Ball.smoothBallCutoff_one d 0 0
      (R := 1) (δ := 1) (by norm_num) (by norm_num) (by simp)
  change Tendsto (fun k ↦ densityCutoff k x) atTop (𝓝 (densityBase (0 • x))) at ht
  rw [zero_smul, hzero] at ht
  exact ht

private theorem densityCutoff_partial_tendsto (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun k ↦ partialD i (densityCutoff k) x) atTop (𝓝 0) := by
  simp_rw [densityCutoff_partial]
  simpa using densityScale_tendsto.mul
    ((densityBase_test.continuous_partialD i).continuousAt.tendsto.comp
      (densityScale_tendsto.smul_const x))

private theorem densityCutoff_partial_bound (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k x, ‖partialD i (densityCutoff (d := d) k) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (densityBase_test.continuous_partialD i).bounded_above_of_compact_support
    (densityBase_test.hasCompactSupport_partialD i)
  refine ⟨max C 0, le_max_right _ _, fun k x ↦ ?_⟩
  rw [densityCutoff_partial, norm_mul, Real.norm_eq_abs, abs_of_pos (densityScale_pos k)]
  exact (mul_le_mul_of_nonneg_left ((hC _).trans (le_max_left _ _))
    (densityScale_pos k).le).trans (mul_le_of_le_one_left (le_max_right _ _)
      (densityScale_le_one k))

private theorem weak_cutoff_product
    {U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))} (hU : U ∈ W12 univ)
    {χ φ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn univ χ)
    (hφ : IsTestFn univ φ) (i : Fin d) :
    (∫ x, (χ x * U 0 x) * partialD i φ x) =
      -(∫ x, (χ x * U i.succ x + partialD i χ x * U 0 x) * φ x) := by
  have hLp (j : Fin (d + 1)) : MemLp (U j) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (U j)
  let htest := isTestFn_mul_smooth hχ hφ.1
  let htesti := isTestFn_mul_smooth hχ (hφ.partialD i).1
  let hχitest := isTestFn_mul_smooth (hχ.partialD i) hφ.1
  have hA : Integrable (fun x ↦ U 0 x * partialD i χ x * φ x) := by
    have h := (hLp 0).integrable_mul (by
      simpa only [Measure.restrict_univ] using hχitest.mem_lp)
    convert h using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hB : Integrable (fun x ↦ U 0 x * χ x * partialD i φ x) := by
    have h := (hLp 0).integrable_mul (by
      simpa only [Measure.restrict_univ] using htesti.mem_lp)
    convert h using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hC : Integrable (fun x ↦ U i.succ x * χ x * φ x) := by
    have h := (hLp i.succ).integrable_mul (by
      simpa only [Measure.restrict_univ] using htest.mem_lp)
    convert h using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hw := weak_gradient_integral_of_mem_W12_univ hU htest i
  simp_rw [partialD_mul_smooth hχ.1 hφ.1, Pi.mul_apply] at hw
  have heq : (fun x ↦ U 0 x * (partialD i χ x * φ x + χ x * partialD i φ x)) =
      (fun x ↦ U 0 x * partialD i χ x * φ x + U 0 x * χ x * partialD i φ x) := by
    funext x
    ring
  rw [heq, integral_add hA hB] at hw
  have heq' : (fun x ↦ (χ x * U i.succ x + partialD i χ x * U 0 x) * φ x) =
      (fun x ↦ U i.succ x * χ x * φ x + U 0 x * partialD i χ x * φ x) := by
    funext x
    ring
  rw [heq', integral_add hC hA]
  have hc : (fun x ↦ χ x * U 0 x * partialD i φ x) =
      (fun x ↦ U 0 x * χ x * partialD i φ x) := by funext x; ring
  rw [hc]
  simp only [← mul_assoc] at hw
  linarith

/-- A genuine smooth spatial cutoff preserves whole-space weak derivative constraints. -/
theorem spatialCutoffAmbientCLM_mem_W12_univ
    {U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))} (hU : U ∈ W12 univ)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn univ χ) :
    spatialCutoffAmbientCLM hχ U ∈ W12 univ := by
  rw [mem_W12_iff]
  intro φ hφ i
  rw [L2.inner_def, L2.inner_def, setIntegral_univ, setIntegral_univ]
  have hae0 : spatialCutoffAmbientCLM hχ U 0 =ᵐ[volume] fun x ↦ χ x * U 0 x := by
    simpa only [Measure.restrict_univ] using spatialCutoffAmbientCLM_value_ae hχ U
  have haei : spatialCutoffAmbientCLM hχ U i.succ =ᵐ[volume]
      fun x ↦ χ x * U i.succ x + partialD i χ x * U 0 x := by
    simpa only [Measure.restrict_univ] using spatialCutoffAmbientCLM_partial_ae hχ U i
  have hφ0 : hφ.testCls =ᵐ[volume] φ := by
    simpa only [IsTestFn.testCls, Measure.restrict_univ] using hφ.mem_lp.coeFn_toLp
  have hφi : hφ.partialCls i =ᵐ[volume] partialD i φ := by
    simpa only [IsTestFn.partialCls, Measure.restrict_univ]
      using (hφ.memLp_partialD i).coeFn_toLp
  have hleft : (∫ x, inner ℝ (hφ.partialCls i x) (spatialCutoffAmbientCLM hχ U 0 x)) =
      ∫ x, (χ x * U 0 x) * partialD i φ x := by
    apply integral_congr_ae
    filter_upwards [hae0, hφi] with x h0 hi
    simp only [Real.inner_apply, h0, hi, mul_comm]
  have hright : (∫ x, inner ℝ (hφ.testCls x) (spatialCutoffAmbientCLM hχ U i.succ x)) =
      ∫ x, (χ x * U i.succ x + partialD i χ x * U 0 x) * φ x := by
    apply integral_congr_ae
    filter_upwards [haei, hφ0] with x hi h0
    simp only [Real.inner_apply, hi, h0, mul_comm]
  rw [hleft, hright]
  linarith [weak_cutoff_product hU hχ hφ i]

private theorem densityGraph_value_tendsto
    (U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) :
    Tendsto (fun k ↦ spatialCutoffAmbientCLM (densityCutoff_test k) U 0)
      atTop (𝓝 (U 0)) := by
  have hLp : MemLp (U 0) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (U 0)
  have hae k : spatialCutoffAmbientCLM (densityCutoff_test k) U 0 =ᵐ[volume]
      fun x ↦ densityCutoff k x * U 0 x := by
    simpa only [Measure.restrict_univ]
      using spatialCutoffAmbientCLM_value_ae (densityCutoff_test k) U
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ (U 0)).mpr
  simp only [Measure.restrict_univ]
  apply tendsto_eLpNorm_two_of_dominated
    (fun k ↦ by simpa only [Measure.restrict_univ] using
      Lp.aestronglyMeasurable (spatialCutoffAmbientCLM (densityCutoff_test k) U 0))
    hLp.aestronglyMeasurable (hLp.norm.const_mul 2)
  · intro k
    filter_upwards [hae k] with x hx
    rw [hx]
    calc
      ‖densityCutoff k x * U 0 x - U 0 x‖ ≤
          ‖densityCutoff k x * U 0 x‖ + ‖U 0 x‖ := norm_sub_le _ _
      _ ≤ 2 * ‖U 0 x‖ := by
        rw [norm_mul]
        nlinarith [densityCutoff_norm k x, norm_nonneg (U 0 x)]
      _ = ‖2 * ‖U 0 x‖‖ := by rw [norm_mul, Real.norm_of_nonneg (norm_nonneg _)]; norm_num
  · filter_upwards [ae_all_iff.mpr hae] with x hx
    simp_rw [hx]
    simpa using (densityCutoff_tendsto x).mul_const (U 0 x)

private theorem densityGraph_partial_tendsto
    (U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) (i : Fin d) :
    Tendsto (fun k ↦ spatialCutoffAmbientCLM (densityCutoff_test k) U i.succ)
      atTop (𝓝 (U i.succ)) := by
  obtain ⟨C, hC, hbound⟩ := densityCutoff_partial_bound i
  have hLp (j : Fin (d + 1)) : MemLp (U j) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (U j)
  have hae k : spatialCutoffAmbientCLM (densityCutoff_test k) U i.succ =ᵐ[volume]
      fun x ↦ densityCutoff k x * U i.succ x + partialD i (densityCutoff k) x * U 0 x := by
    simpa only [Measure.restrict_univ]
      using spatialCutoffAmbientCLM_partial_ae (densityCutoff_test k) U i
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ (U i.succ)).mpr
  simp only [Measure.restrict_univ]
  apply tendsto_eLpNorm_two_of_dominated
    (fun k ↦ by simpa only [Measure.restrict_univ] using
      Lp.aestronglyMeasurable (spatialCutoffAmbientCLM (densityCutoff_test k) U i.succ))
    (hLp i.succ).aestronglyMeasurable
    (((hLp i.succ).norm.const_mul 2).add ((hLp 0).norm.const_mul C))
  · intro k
    filter_upwards [hae k] with x hx
    rw [hx]
    calc
      ‖densityCutoff k x * U i.succ x + partialD i (densityCutoff k) x * U 0 x -
          U i.succ x‖ ≤ ‖densityCutoff k x * U i.succ x‖ +
          ‖partialD i (densityCutoff k) x * U 0 x‖ + ‖U i.succ x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 * ‖U i.succ x‖ + C * ‖U 0 x‖ := by
        simp only [norm_mul]
        nlinarith [densityCutoff_norm k x, hbound k x,
          norm_nonneg (U i.succ x), norm_nonneg (U 0 x)]
      _ = ‖2 * ‖U i.succ x‖ + C * ‖U 0 x‖‖ := by
        exact (Real.norm_of_nonneg (show 0 ≤ 2 * ‖U i.succ x‖ + C * ‖U 0 x‖
          from add_nonneg (by positivity) (mul_nonneg hC (norm_nonneg _)))).symm
  · filter_upwards [ae_all_iff.mpr hae] with x hx
    simp_rw [hx]
    simpa using ((densityCutoff_tendsto x).mul_const (U i.succ x)).add
      ((densityCutoff_partial_tendsto i x).mul_const (U 0 x))

/-- Every actual whole-space weak derivative graph is in the genuine compact-test closure. -/
theorem mem_H01_univ_of_mem_W12
    {U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))} (hU : U ∈ W12 univ) :
    U ∈ H01 univ := by
  have hcut k : spatialCutoffAmbientCLM (densityCutoff_test k) U ∈ H01 univ := by
    apply mem_H01_univ_of_compact_weak_graph
      (spatialCutoffAmbientCLM_mem_W12_univ hU (densityCutoff_test k))
      (densityCutoff_test k).2.1
    have hae : spatialCutoffAmbientCLM (densityCutoff_test k) U 0 =ᵐ[volume]
        fun x ↦ densityCutoff k x * U 0 x := by
      simpa only [Measure.restrict_univ]
        using spatialCutoffAmbientCLM_value_ae (densityCutoff_test k) U
    filter_upwards [hae] with x hx
    intro hxs
    rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (b := atTop) _ (Eventually.of_forall hcut)
  apply ((PiLp.continuous_toLp 2
    (fun _ : Fin (d + 1) ↦ L2D (univ : Set (EuclideanSpace ℝ (Fin d))))).tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro j
  induction j using Fin.cases with
  | zero => exact densityGraph_value_tendsto U
  | succ i => exact densityGraph_partial_tendsto U i

/-- On the whole Euclidean space the genuine zero-boundary closure equals the weak graph space. -/
theorem H01_univ_eq_W12 :
    H01 (univ : Set (EuclideanSpace ℝ (Fin d))) = W12 univ :=
  le_antisymm (H01_le_W12 _) fun _ ↦ mem_H01_univ_of_mem_W12

end PartialBalayage.Linear
