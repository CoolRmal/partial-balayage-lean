/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The genuine dense L¹ and L² input space

The submodule consists of actual square-integrable classes whose representatives are
integrable. Its map into L¹ reads the same almost everywhere class. Integrable simple
functions prove that this map has dense range on arbitrary ambient measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {X E 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The actual intersection of L¹ with the square-integrable input classes. -/
def integrableL2Submodule : Submodule 𝕜 (Lp E 2 μ) where
  carrier := {f | Integrable (f : X → E) μ}
  zero_mem' := (integrable_zero X E μ).congr
    (Lp.coeFn_zero E 2 μ).symm
  add_mem' hf hg := (hf.add hg).congr (Lp.coeFn_add _ _).symm
  smul_mem' c _ hf := (hf.smul c).congr (Lp.coeFn_smul _ _).symm

/-- Read an actual integrable square-integrable class as an L¹ class. -/
def integrableL2ToL1 : integrableL2Submodule (𝕜 := 𝕜) (E := E) (μ := μ) →ₗ[𝕜] Lp E 1 μ where
  toFun f := (show Integrable (f.val : X → E) μ from f.property).toL1 f.val
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(f + g).property.coeFn_toL1, f.property.coeFn_toL1,
      g.property.coeFn_toL1, Lp.coeFn_add f.val g.val,
      Lp.coeFn_add (f.property.toL1 f.val) (g.property.toL1 g.val)] with x hfg hf hg ha hb
    rw [hfg, hb, Pi.add_apply, hf, hg]
    exact ha
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(c • f).property.coeFn_toL1, f.property.coeFn_toL1,
      Lp.coeFn_smul c f.val, Lp.coeFn_smul c (f.property.toL1 f.val)] with x hcf hf ha hb
    rw [hcf, hb, Pi.smul_apply, hf]
    exact ha

/-- This L¹ input map preserves the actual representative almost everywhere. -/
theorem integrableL2ToL1_ae
    (f : integrableL2Submodule (𝕜 := 𝕜) (E := E) (μ := μ)) :
    integrableL2ToL1 f =ᵐ[μ] (f.val : X → E) := f.property.coeFn_toL1

/-- Every integrable simple L¹ input is represented by a genuine integrable L² input. -/
theorem simpleFunc_mem_range_integrableL2ToL1 (f : Lp.simpleFunc E 1 μ) :
    (f : Lp E 1 μ) ∈ range (integrableL2ToL1 (𝕜 := 𝕜) (E := E) (μ := μ)) := by
  let s := Lp.simpleFunc.toSimpleFunc f
  have hs : Integrable s μ := L1.SimpleFunc.integrable f
  have hs2 : MemLp s 2 μ :=
    (SimpleFunc.memLp_iff_integrable (by norm_num) (by norm_num)).mpr hs
  let u : integrableL2Submodule (𝕜 := 𝕜) (E := E) (μ := μ) :=
    ⟨hs2.toLp s, hs.congr hs2.coeFn_toLp.symm⟩
  refine ⟨u, ?_⟩
  apply Lp.ext
  exact (integrableL2ToL1_ae u).trans
    (hs2.coeFn_toLp.trans (Lp.simpleFunc.toSimpleFunc_eq_toFun f))

/-- Actual integrable L² classes are dense in the full L¹ input space. -/
theorem denseRange_integrableL2ToL1 :
    DenseRange (integrableL2ToL1 (𝕜 := 𝕜) (E := E) (μ := μ)) := by
  apply (Lp.simpleFunc.denseRange (E := E) (μ := μ) (p := 1) (by norm_num)).mono
  rintro _ ⟨f, rfl⟩
  exact simpleFunc_mem_range_integrableL2ToL1 f

/-- Every actual L¹ class has actual integrable L² approximations in L¹ norm. -/
theorem exists_integrableL2_approximation (f : Lp E 1 μ) :
    ∃ u : ℕ → integrableL2Submodule (𝕜 := 𝕜) (E := E) (μ := μ),
      Tendsto (fun n ↦ integrableL2ToL1 (u n)) atTop (𝓝 f) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_integrableL2ToL1 (𝕜 := 𝕜) f)
  choose u hu using hv
  refine ⟨u, ?_⟩
  convert hlim using 1
  exact funext hu

end PartialBalayage.Linear
