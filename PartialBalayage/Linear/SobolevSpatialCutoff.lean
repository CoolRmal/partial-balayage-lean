/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LocalCutoffEquation
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

/-!
# Actual spatial cutoffs in the Dirichlet Sobolev graph

Multiplication by a smooth compact interior cutoff is a bounded linear map on the ambient
value-gradient graph. The classical product rule preserves test-function graphs. Continuity
then preserves their defining closure, constructing an actual `H01` element with the product
value and gradient, all supported almost everywhere inside the cutoff's support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- A uniformly bounded measurable scalar preserves actual square integrability. -/
theorem boundedScalar_memLp (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : AEStronglyMeasurable φ (volume.restrict Ω)) (C : ℝ)
    (hC : ∀ x, ‖φ x‖ ≤ C) (f : L2D Ω) :
    MemLp (fun x ↦ φ x * f x) 2 (volume.restrict Ω) := by
  apply (Lp.memLp f).of_le_mul (hφ.mul (Lp.aestronglyMeasurable f))
  filter_upwards with x
  change ‖φ x * f x‖ ≤ C * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Pointwise multiplication of an actual `L²` function by a bounded measurable scalar. -/
def boundedScalarL2 (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : AEStronglyMeasurable φ (volume.restrict Ω)) (C : ℝ)
    (hC : ∀ x, ‖φ x‖ ≤ C) (f : L2D Ω) : L2D Ω :=
  (boundedScalar_memLp φ hφ C hC f).toLp (fun x ↦ φ x * f x)

private theorem boundedScalarL2_ae (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : AEStronglyMeasurable φ (volume.restrict Ω)) (C : ℝ)
    (hC : ∀ x, ‖φ x‖ ≤ C) (f : L2D Ω) :
    boundedScalarL2 φ hφ C hC f =ᵐ[volume.restrict Ω] fun x ↦ φ x * f x :=
  (boundedScalar_memLp φ hφ C hC f).coeFn_toLp

/-- The linear map underlying bounded scalar multiplication on `L²`. -/
def boundedScalarL2Linear (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : AEStronglyMeasurable φ (volume.restrict Ω)) (C : ℝ)
    (hC : ∀ x, ‖φ x‖ ≤ C) : L2D Ω →ₗ[ℝ] L2D Ω where
  toFun := boundedScalarL2 φ hφ C hC
  map_add' f g := by
    apply Lp.ext
    filter_upwards [boundedScalarL2_ae φ hφ C hC (f + g),
      boundedScalarL2_ae φ hφ C hC f, boundedScalarL2_ae φ hφ C hC g,
      Lp.coeFn_add f g, Lp.coeFn_add (boundedScalarL2 φ hφ C hC f)
        (boundedScalarL2 φ hφ C hC g)] with x hfg hf hg hsum hsum'
    simp only [Pi.add_apply] at hsum hsum'
    rw [hsum', hfg, hf, hg, hsum]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [boundedScalarL2_ae φ hφ C hC (c • f),
      boundedScalarL2_ae φ hφ C hC f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (boundedScalarL2 φ hφ C hC f)] with x hcf hf hs hs'
    simp only [Pi.smul_apply, smul_eq_mul] at hs hs'
    change boundedScalarL2 φ hφ C hC (c • f) x =
      (c • boundedScalarL2 φ hφ C hC f) x
    rw [hs', hcf, hf, hs]
    ring

/-- Bounded measurable scalar multiplication is a continuous linear map on `L²`. -/
def boundedScalarL2CLM (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : AEStronglyMeasurable φ (volume.restrict Ω)) (C : ℝ)
    (hC : ∀ x, ‖φ x‖ ≤ C) : L2D Ω →L[ℝ] L2D Ω :=
  (boundedScalarL2Linear φ hφ C hC).mkContinuous C (by
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [boundedScalarL2_ae φ hφ C hC f] with x hx
    change ‖boundedScalarL2 φ hφ C hC f x‖ ≤ C * ‖f x‖
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- Multiplication by a continuous compactly supported scalar on actual `L²`. -/
def compactScalarL2CLM (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : Continuous φ) (hsupp : HasCompactSupport φ) : L2D Ω →L[ℝ] L2D Ω :=
  boundedScalarL2CLM φ hφ.aestronglyMeasurable
    (Classical.choose (hφ.bounded_above_of_compact_support hsupp))
    (Classical.choose_spec (hφ.bounded_above_of_compact_support hsupp))

private theorem compactScalarL2CLM_ae (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : Continuous φ) (hsupp : HasCompactSupport φ) (f : L2D Ω) :
    compactScalarL2CLM φ hφ hsupp f =ᵐ[volume.restrict Ω] fun x ↦ φ x * f x :=
  boundedScalarL2_ae φ hφ.aestronglyMeasurable
    (Classical.choose (hφ.bounded_above_of_compact_support hsupp))
    (Classical.choose_spec (hφ.bounded_above_of_compact_support hsupp)) f

/-- The bounded spatial product map on actual value-gradient graphs. -/
def spatialCutoffAmbientCLM {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) : H1amb Ω →L[ℝ] H1amb Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ L2D Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (Fin.cons
      (compactScalarL2CLM χ hχ.continuous hχ.2.1 ∘L
        PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) 0)
      (fun i ↦ compactScalarL2CLM χ hχ.continuous hχ.2.1 ∘L
        PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) i.succ +
          compactScalarL2CLM (partialD i χ) (hχ.continuous_partialD i)
            (hχ.hasCompactSupport_partialD i) ∘L
              PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) 0))

/-- The ambient cutoff map has the genuine pointwise product value. -/
theorem spatialCutoffAmbientCLM_value_ae {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (U : H1amb Ω) :
    spatialCutoffAmbientCLM hχ U 0 =ᵐ[volume.restrict Ω] fun x ↦ χ x * U 0 x := by
  change compactScalarL2CLM χ hχ.continuous hχ.2.1 (U 0) =ᵐ[volume.restrict Ω]
    fun x ↦ χ x * U 0 x
  exact compactScalarL2CLM_ae χ hχ.continuous hχ.2.1 (U 0)

/-- The ambient cutoff map has the genuine weak-gradient product formula. -/
theorem spatialCutoffAmbientCLM_partial_ae {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (U : H1amb Ω) (i : Fin d) :
    spatialCutoffAmbientCLM hχ U i.succ =ᵐ[volume.restrict Ω]
      fun x ↦ χ x * U i.succ x + partialD i χ x * U 0 x := by
  change (compactScalarL2CLM χ hχ.continuous hχ.2.1 (U i.succ) +
    compactScalarL2CLM (partialD i χ) (hχ.continuous_partialD i)
      (hχ.hasCompactSupport_partialD i) (U 0) : L2D Ω) =ᵐ[volume.restrict Ω] _
  filter_upwards [compactScalarL2CLM_ae χ hχ.continuous hχ.2.1 (U i.succ),
    compactScalarL2CLM_ae (partialD i χ) (hχ.continuous_partialD i)
      (hχ.hasCompactSupport_partialD i) (U 0),
    Lp.coeFn_add (compactScalarL2CLM χ hχ.continuous hχ.2.1 (U i.succ))
      (compactScalarL2CLM (partialD i χ) (hχ.continuous_partialD i)
        (hχ.hasCompactSupport_partialD i) (U 0))] with x hvalue hpartial hadd
  simp only [Pi.add_apply] at hadd
  rw [hadd, hvalue, hpartial]

/-- The spatial product map sends a test graph to the actual graph of the product test. -/
theorem spatialCutoffAmbientCLM_testGraph {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (hφ : IsTestFn Ω φ) :
    spatialCutoffAmbientCLM hχ hφ.testGraph = (isTestFn_mul_smooth hχ hφ.1).testGraph := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · filter_upwards [spatialCutoffAmbientCLM_value_ae hχ hφ.testGraph,
      hφ.mem_lp.coeFn_toLp, (isTestFn_mul_smooth hχ hφ.1).mem_lp.coeFn_toLp]
        with x hvalue hφvalue hproduct
    simp only [IsTestFn.testGraph_zero, IsTestFn.testCls] at hvalue ⊢
    rw [hvalue, hφvalue, hproduct]
    rfl
  · filter_upwards [spatialCutoffAmbientCLM_partial_ae hχ hφ.testGraph i,
      hφ.mem_lp.coeFn_toLp, (hφ.memLp_partialD i).coeFn_toLp,
      ((isTestFn_mul_smooth hχ hφ.1).memLp_partialD i).coeFn_toLp]
        with x hpartial hφvalue hφpartial hproduct
    simp only [IsTestFn.testGraph_succ, IsTestFn.testGraph_zero, IsTestFn.testCls,
      IsTestFn.partialCls] at hpartial ⊢
    rw [hpartial, hφvalue, hφpartial, hproduct, partialD_mul_smooth hχ.1 hφ.1]
    ring

/-- Continuity and preservation of test graphs give actual Dirichlet graph membership. -/
theorem spatialCutoffAmbientCLM_mem_H01 {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    spatialCutoffAmbientCLM hχ U ∈ H01 Ω := by
  have hcl : U ∈ closure (testGraphSet Ω) := by
    have hcl' : U ∈ closure ((Submodule.span ℝ (testGraphSet Ω)) : Set (H1amb Ω)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hU
    rw [span_testGraphSet] at hcl'
    exact hcl'
  have himage : spatialCutoffAmbientCLM hχ '' testGraphSet Ω ⊆ (H01 Ω : Set (H1amb Ω)) := by
    rintro W ⟨X, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [spatialCutoffAmbientCLM_testGraph hχ hφ]
    exact (isTestFn_mul_smooth hχ hφ.1).toH01.property
  exact (closure_minimal himage (Submodule.isClosed_topologicalClosure _))
    ((image_closure_subset_closure_image (spatialCutoffAmbientCLM hχ).continuous)
      ⟨U, hcl, rfl⟩)

/-- The actual bounded spatial-cutoff operator on the Dirichlet Sobolev space. -/
def spatialCutoffH01 {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) : H01 Ω →L[ℝ] H01 Ω :=
  (spatialCutoffAmbientCLM hχ).restrict fun _ hU ↦ spatialCutoffAmbientCLM_mem_H01 hχ hU

/-- The actual Dirichlet cutoff has the product value almost everywhere. -/
theorem spatialCutoffH01_value_ae {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (U : H01 Ω) :
    ((spatialCutoffH01 hχ U : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x ↦ χ x * (U : H1amb Ω) 0 x :=
  spatialCutoffAmbientCLM_value_ae hχ (U : H1amb Ω)

/-- The actual Dirichlet cutoff has the weak-gradient product formula almost everywhere. -/
theorem spatialCutoffH01_partial_ae {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (U : H01 Ω) (i : Fin d) :
    ((spatialCutoffH01 hχ U : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x ↦ χ x * (U : H1amb Ω) i.succ x +
        partialD i χ x * (U : H1amb Ω) 0 x :=
  spatialCutoffAmbientCLM_partial_ae hχ (U : H1amb Ω) i

/-- Every coordinate of the actual cutoff graph vanishes almost everywhere off its support. -/
theorem spatialCutoffH01_supported_ae {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (U : H01 Ω) (j : Fin (d + 1)) :
    ∀ᵐ x ∂volume.restrict Ω, x ∉ tsupport χ →
      ((spatialCutoffH01 hχ U : H1amb Ω) j x : ℝ) = 0 := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · filter_upwards [spatialCutoffH01_value_ae hχ U] with x hx
    intro hxs
    rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  · filter_upwards [spatialCutoffH01_partial_ae hχ U i] with x hx
    intro hxs
    have hpartial : partialD i χ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hxs (tsupport_partialD_subset i χ h))
    rw [hx, image_eq_zero_of_notMem_tsupport hxs, hpartial]
    ring

/-- A genuine spatial cutoff graph exists, with actual value, gradient, and compact support. -/
theorem exists_H01_spatial_cutoff (U : H01 Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    ∃ V : H01 Ω,
      ((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (fun x ↦ χ x * (U : H1amb Ω) 0 x) ∧
      (∀ i : Fin d, ((V : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x ↦ χ x * (U : H1amb Ω) i.succ x +
          partialD i χ x * (U : H1amb Ω) 0 x) ∧
      ∀ j : Fin (d + 1), ∀ᵐ x ∂volume.restrict Ω, x ∉ tsupport χ →
        ((V : H1amb Ω) j x : ℝ) = 0 :=
  ⟨spatialCutoffH01 hχ U, spatialCutoffH01_value_ae hχ U,
    spatialCutoffH01_partial_ae hχ U, spatialCutoffH01_supported_ae hχ U⟩

end PartialBalayage.Linear
