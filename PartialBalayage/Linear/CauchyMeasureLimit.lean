/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Genuine almost everywhere limits of Cauchy sequences in measure

The fast subsequence is selected from the actual Cauchy estimates. Borel--Cantelli
makes its successive distances summable almost everywhere, and completeness of the
output space then produces an actual strongly measurable limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A genuine global Cauchy condition in measure, with real distance thresholds. -/
def IsCauchyInMeasure [PseudoMetricSpace E] (f : ℕ → X → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ≥0∞, 0 < δ →
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, μ {x | ε < dist (f m x) (f n x)} < δ

/-- Summable geometric increment estimates give a genuine measurable a.e. limit. -/
theorem exists_stronglyMeasurable_limit_of_geometric_increment
    [MetricSpace E] [CompleteSpace E] (f : ℕ → X → E)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hb : ∀ n, μ {x | (1 / 2 : ℝ) ^ n < dist (f n x) (f (n + 1) x)} ≤
      (2 : ℝ≥0∞)⁻¹ ^ n) :
    ∃ g : X → E, StronglyMeasurable g ∧
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  have hsum : (∑' n, μ {x | (1 / 2 : ℝ) ^ n < dist (f n x) (f (n + 1) x)}) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hb)
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ⊤)
  have hae := ae_eventually_notMem hsum
  apply exists_stronglyMeasurable_limit_of_tendsto_ae hf
  filter_upwards [hae] with x hx
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_summable_dist
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [hx] with n hn
  simpa only [mem_ofPred_eq, not_lt, Real.norm_of_nonneg (dist_nonneg)] using hn

/-- Every genuine Cauchy sequence in measure has a strongly measurable a.e. subsequential limit. -/
theorem IsCauchyInMeasure.exists_stronglyMeasurable_subsequence_limit
    [MetricSpace E] [CompleteSpace E] {f : ℕ → X → E}
    (hc : IsCauchyInMeasure (μ := μ) f)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : X → E, StronglyMeasurable g ∧
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ f (ns n) x) atTop (𝓝 (g x)) := by
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      μ {x | (1 / 2 : ℝ) ^ k < dist (f m x) (f n x)} < (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    exact hc _ (by positivity) _ (ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) k)
  choose N hN using hN
  let ns : ℕ → ℕ := Nat.rec (N 0) (fun k prev ↦ max (N (k + 1)) (prev + 1))
  have hns : ∀ k, N k ≤ ns k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_left _ _
  have hmono : StrictMono ns := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact (Nat.lt_succ_self (ns k)).trans_le (le_max_right _ _)
  obtain ⟨g, hg, hfg⟩ := exists_stronglyMeasurable_limit_of_geometric_increment
    (fun k ↦ f (ns k)) (fun k ↦ hf (ns k)) (fun k ↦
      (hN k (ns k) (hns k) (ns (k + 1))
        ((hns k).trans (hmono.monotone (Nat.le_succ k)))).le)
  exact ⟨ns, hmono, g, hg, hfg⟩

/-- Outer measure is lower semicontinuous under a.e. eventual inclusion of sets. -/
theorem measure_le_liminf_of_ae_eventually_mem (s : Set X) (u : ℕ → Set X)
    (h : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in atTop, x ∈ u n) :
    μ s ≤ liminf (fun n ↦ μ (u n)) atTop := by
  have hsub : s ≤ᵐ[μ] ⋃ N : ℕ, ⋂ n ≥ N, u n := by
    filter_upwards [h] with x hx
    intro hxs
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hx hxs)
    exact mem_iUnion.mpr ⟨N, mem_iInter.mpr fun n ↦ mem_iInter.mpr (hN n)⟩
  have hmono : Monotone (fun N : ℕ ↦ ⋂ n ≥ N, u n) := by
    intro N M hNM x hx
    exact mem_iInter.mpr fun n ↦ mem_iInter.mpr fun hn ↦
      mem_iInter.mp (mem_iInter.mp hx n) (hNM.trans hn)
  calc
    μ s ≤ μ (⋃ N : ℕ, ⋂ n ≥ N, u n) := measure_mono_ae hsub
    _ = ⨆ N : ℕ, μ (⋂ n ≥ N, u n) := hmono.measure_iUnion
    _ ≤ ⨆ N : ℕ, ⨅ n ≥ N, μ (u n) := by
      apply iSup_mono
      intro N
      exact le_iInf fun n ↦ le_iInf fun hn ↦ measure_mono (iInter₂_subset n hn)
    _ = liminf (fun n ↦ μ (u n)) atTop := liminf_eq_iSup_iInf_of_nat.symm

/-- Actual a.e. convergence passes the strict norm level measure to the liminf. -/
theorem measure_norm_level_le_liminf_of_ae_tendsto [NormedAddCommGroup E]
    (f : ℕ → X → E) (g : X → E)
    (h : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) (r : ℝ) :
    μ {x | r < ‖g x‖} ≤ liminf (fun n ↦ μ {x | r < ‖f n x‖}) atTop := by
  apply measure_le_liminf_of_ae_eventually_mem
  filter_upwards [h] with x hx
  intro hxr
  exact hx.norm.eventually (lt_mem_nhds hxr)

/-- Vanishing actual level measures identify a genuine a.e. sequential limit with zero. -/
theorem ae_eq_zero_of_ae_tendsto_of_level_measures_tendsto_zero [NormedAddCommGroup E]
    (f : ℕ → X → E) (g : X → E)
    (h : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hlevel : ∀ r : ℝ, 0 < r →
      Tendsto (fun n ↦ μ {x | r < ‖f n x‖}) atTop (𝓝 0)) : g =ᵐ[μ] 0 := by
  have hz : ∀ k : ℕ, μ {x | (1 / 2 : ℝ) ^ k < ‖g x‖} = 0 := by
    intro k
    apply le_antisymm _ zero_le
    have hb := measure_norm_level_le_liminf_of_ae_tendsto f g h ((1 / 2 : ℝ) ^ k)
    have hr : 0 < (1 / 2 : ℝ) ^ k := by positivity
    rw [(hlevel ((1 / 2 : ℝ) ^ k) hr).liminf_eq] at hb
    exact hb
  have hae : ∀ᵐ x ∂μ, ∀ k : ℕ, ‖g x‖ ≤ (1 / 2 : ℝ) ^ k := by
    apply ae_all_iff.mpr
    intro k
    simpa only [mem_ofPred_eq, not_lt] using (measure_eq_zero_iff_ae_notMem.mp (hz k))
  filter_upwards [hae] with x hx
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)) hx

end PartialBalayage.Linear
