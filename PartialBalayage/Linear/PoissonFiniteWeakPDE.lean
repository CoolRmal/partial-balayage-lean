/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.H01PoissonGenerator
public import PartialBalayage.Linear.PoissonStateExhaustion

/-!
# Actual compact-test equation passage for signed Poisson obstacles

The true bounded finite equations transport to global tests supported in their domains.
Uniform ordinary `L²` state bounds permit a genuinely strong-varying generator test to
pair against the weak state limit. The actual Poisson generator limit therefore passes
the same finite equations to physical whole-space compact tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace Topology

namespace PartialBalayage.Linear

/-- A uniformly bounded actual weak sequence pairs continuously with a genuine strong test limit. -/
theorem tendsto_inner_of_weak_strong_bounded {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {l : Filter ι}
    {u v : ι → E} {ulimit vlimit : E} {B : ℝ}
    (hut : Tendsto (fun k ↦ toWeakSpace ℝ E (u k)) l (𝓝 (toWeakSpace ℝ E ulimit)))
    (hvt : Tendsto v l (𝓝 vlimit)) (hB : ∀ k, ‖u k‖ ≤ B) :
    Tendsto (fun k ↦ ⟪u k, v k⟫) l (𝓝 ⟪ulimit, vlimit⟫) := by
  have hfix : Tendsto (fun k ↦ ⟪vlimit, u k⟫) l (𝓝 ⟪vlimit, ulimit⟫) :=
    ((innerSL ℝ vlimit).continuous_comp_toWeakSpace_symm.tendsto _).comp hut
  have hdelta : Tendsto (fun k ↦ ⟪u k, v k - vlimit⟫) l (𝓝 0) := by
    apply squeeze_zero_norm (fun k ↦ (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hB k) (norm_nonneg (v k - vlimit))))
    simpa only [sub_self, norm_zero, mul_zero] using
      (hvt.sub (tendsto_const_nhds (x := vlimit))).norm.const_mul B
  have h := hfix.add hdelta
  have he : (fun k ↦ ⟪vlimit, u k⟫ + ⟪u k, v k - vlimit⟫) =
      (fun k ↦ ⟪u k, v k⟫) := by
    funext k
    rw [inner_sub_right, real_inner_comm (u k) vlimit]
    ring
  simpa only [he, add_zero, real_inner_comm ulimit vlimit] using h

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℝ 2 (volume : Measure D)

/-- Restriction recovers the original actual finite class from its zero extension. -/
theorem restrictL2_zeroExtend {Ω : Set D} (hΩ : MeasurableSet Ω)
    (u : Lp ℝ 2 (volume.restrict Ω)) : restrictL2CLM Ω (zeroExtendL2 hΩ u) = u :=
  Lp.ext ((restrictL2CLM_ae Ω _).trans (zeroExtendL2_ae_restrict_value hΩ u))

/-- Actual support makes zero extension of genuine domain restriction exactly the original class. -/
theorem zeroExtend_restrictL2_of_ae_support {Ω : Set D} (hΩ : MeasurableSet Ω)
    (φ : L²) (hs : ∀ᵐ x, x ∉ Ω → φ x = 0) :
    zeroExtendL2 hΩ (restrictL2CLM Ω φ) = φ := by
  have hr : ∀ᵐ x, x ∈ Ω → restrictL2CLM Ω φ x = φ x :=
    (ae_restrict_iff' hΩ).mp (restrictL2CLM_ae Ω φ)
  apply Lp.ext
  filter_upwards [zeroExtendL2_ae hΩ (restrictL2CLM Ω φ), hr, hs] with x hx hr hs
  rw [hx]
  by_cases hxo : x ∈ Ω
  · rw [indicator_of_mem hxo, hr hxo]
  · rw [indicator_of_notMem hxo, hs hxo]

/-- The actual finite equation is a genuine global generator equation against supported tests. -/
theorem poissonDirichlet_global_pairing {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t ε : ℝ} (ht : 0 < t) (f φ : L²) (ν u : Lp ℝ 2 (volume.restrict Ω))
    (heq : poissonDirichletOperator hΩ ht ε u = restrictL2CLM Ω f - ν)
    (hs : ∀ᵐ x, x ∉ Ω → φ x = 0) :
    ε * ⟪zeroExtendL2 hΩ u, φ⟫ +
      ⟪zeroExtendL2 hΩ u, poissonRealQuotientL2CLM ht φ⟫ =
        ⟪f, φ⟫ - ⟪zeroExtendL2 hΩ ν, φ⟫ := by
  let v := restrictL2CLM Ω φ
  have hv : zeroExtendL2 hΩ v = φ := zeroExtend_restrictL2_of_ae_support hΩ φ hs
  have hu : ⟪u, v⟫ = ⟪zeroExtendL2 hΩ u, φ⟫ := by
    rw [← hv, real_inner_comm, inner_global_zeroExtendL2 hΩ, restrictL2_zeroExtend,
      real_inner_comm]
  have hν : ⟪ν, v⟫ = ⟪zeroExtendL2 hΩ ν, φ⟫ := by
    rw [← hv, real_inner_comm, inner_global_zeroExtendL2 hΩ, restrictL2_zeroExtend,
      real_inner_comm]
  have hf : ⟪restrictL2CLM Ω f, v⟫ = ⟪f, φ⟫ := by
    rw [← hv, inner_global_zeroExtendL2]
  have hP : ⟪poissonDirichletAverage hΩ ht u, v⟫ =
      ⟪zeroExtendL2 hΩ u, poissonConvolutionL2 ht φ⟫ := by
    change ⟪restrictL2CLM Ω (poissonConvolutionL2 ht (zeroExtendL2 hΩ u)), v⟫ = _
    rw [← inner_global_zeroExtendL2 hΩ, hv, ← real_inner_poissonConvolutionL2]
  have h := congrArg (fun z : Lp ℝ 2 (volume.restrict Ω) ↦ ⟪z, v⟫) heq
  rw [inner_poissonDirichletOperator, inner_sub_left, hu, hP, hf, hν] at h
  change ε * ⟪zeroExtendL2 hΩ u, φ⟫ +
    ⟪zeroExtendL2 hΩ u, t⁻¹ • (φ - poissonConvolutionL2 ht φ)⟫ = _
  rw [real_inner_smul_right, inner_sub_right]
  exact h

/-- The true joint weak limit satisfies the actual generator equation for every supported
physical test, using the genuine strong Poisson quotient limit. -/
theorem poisson_generator_pairing_of_joint_limit
    (Ω : ℕ → Set D) (hΩ : ∀ k, MeasurableSet (Ω k))
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
    (ν u : ∀ k, Lp ℝ 2 (volume.restrict (Ω k))) (f νlimit limit : L²)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hheight : Tendsto t atTop (𝓝 0))
    (hνt : Tendsto (fun k ↦ toWeakSpace ℝ L² (zeroExtendL2 (hΩ k) (ν k))) l
      (𝓝 (toWeakSpace ℝ L² νlimit)))
    (hut : Tendsto (fun k ↦ toWeakSpace ℝ L² (zeroExtendL2 (hΩ k) (u k))) l
      (𝓝 (toWeakSpace ℝ L² limit))) (B : ℝ)
    (hB : ∀ k, ‖zeroExtendL2 (hΩ k) (u k)‖ ≤ B)
    (heq : ∀ k, poissonDirichletOperator (hΩ k) (ht k) (t k) (u k) =
      restrictL2CLM (Ω k) f - ν k) (W : H01 (univ : Set D))
    (hs : ∀ᶠ k in atTop, ∀ᵐ x, x ∉ Ω k → h01RealValueCLM W x = 0) :
    ⟪limit, h01PoissonRealGeneratorCLM W⟫ = ⟪f - νlimit, h01RealValueCLM W⟫ := by
  have htz := hheight.mono_left hl
  have htr : Tendsto t l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨htz, Eventually.of_forall ht⟩
  have hQt : Tendsto (fun k ↦ poissonRealQuotientL2CLM (ht k) (h01RealValueCLM W)) l
      (𝓝 (h01PoissonRealGeneratorCLM W)) := by
    have h := (tendsto_h01PoissonRealQuotient W).comp htr
    simpa only [Function.comp_def, dite_eq_left (ht _)] using h
  have hQ := tendsto_inner_of_weak_strong_bounded hut hQt hB
  have hU : Tendsto (fun k ↦ ⟪h01RealValueCLM W, zeroExtendL2 (hΩ k) (u k)⟫) l
      (𝓝 ⟪h01RealValueCLM W, limit⟫) :=
    ((innerSL ℝ (h01RealValueCLM W)).continuous_comp_toWeakSpace_symm.tendsto _).comp hut
  have hν : Tendsto (fun k ↦ ⟪h01RealValueCLM W, zeroExtendL2 (hΩ k) (ν k)⟫) l
      (𝓝 ⟪h01RealValueCLM W, νlimit⟫) :=
    ((innerSL ℝ (h01RealValueCLM W)).continuous_comp_toWeakSpace_symm.tendsto _).comp hνt
  have hleft := (htz.mul hU).add hQ
  have hright := (tendsto_const_nhds (x := ⟪f, h01RealValueCLM W⟫)).sub hν
  have hglobal : ∀ᶠ k in l,
      t k * ⟪h01RealValueCLM W, zeroExtendL2 (hΩ k) (u k)⟫ +
        ⟪zeroExtendL2 (hΩ k) (u k), poissonRealQuotientL2CLM (ht k) (h01RealValueCLM W)⟫ =
      ⟪f, h01RealValueCLM W⟫ - ⟪h01RealValueCLM W, zeroExtendL2 (hΩ k) (ν k)⟫ := by
    filter_upwards [hs.filter_mono hl] with k hk
    simpa only [real_inner_comm (zeroExtendL2 (hΩ k) (u k)) (h01RealValueCLM W),
      real_inner_comm (zeroExtendL2 (hΩ k) (ν k)) (h01RealValueCLM W)] using
      poissonDirichlet_global_pairing (hΩ k) (ht k) f _ (ν k) (u k) (heq k) hk
  have he := tendsto_nhds_unique_of_eventuallyEq hleft hright hglobal
  simpa only [zero_mul, zero_add, real_inner_comm νlimit (h01RealValueCLM W),
    ← inner_sub_left] using he

end PartialBalayage.Linear
