/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# Parameters for radial harmonic majorants

The dimension parameter `rho` gives the ratio of the joining radius squared to the
tangency radius squared for the Poisson and heat majorants.
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PartialBalayage.Constants

/-- Ratio of the outer and inner squared radii in the radial majorants. -/
def rho (n : ℕ) : ℝ :=
  if n = 2 then Real.exp 1 else ((n : ℝ) / 2) ^ (2 / ((n : ℝ) - 2))

/-- In dimension one the squared-radius ratio is four. -/
theorem rho_one : rho 1 = 4 := by
  norm_num [rho, Real.rpow_neg_natCast]

/-- The logarithmic planar majorant has squared-radius ratio `exp 1`. -/
theorem rho_two : rho 2 = Real.exp 1 := by
  simp [rho]

/-- Every positive dimension has a positive radial ratio. -/
theorem rho_pos (n : ℕ) (hn : 1 ≤ n) : 0 < rho n := by
  unfold rho
  split_ifs
  · exact Real.exp_pos _
  · apply Real.rpow_pos_of_pos
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity

/-- The outer joining radius exceeds the tangency radius in every positive dimension. -/
theorem one_lt_rho (n : ℕ) (hn : 1 ≤ n) : 1 < rho n := by
  rcases eq_or_lt_of_le hn with hn | hn
  · subst n
    norm_num [rho_one]
  · by_cases hn2 : n = 2
    · rw [hn2, rho_two]
      exact Real.one_lt_exp_iff.mpr zero_lt_one
    · have hn3 : 3 ≤ n := by omega
      have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      simp only [rho, ite_eq_right hn2]
      exact Real.one_lt_rpow (by linarith) (div_pos (by norm_num) (by linarith))

/-- The radial parameter is characterized by the harmonic exponent outside dimension two. -/
theorem rho_rpow_one_sub_half (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≠ 2) :
    rho n ^ (1 - (n : ℝ) / 2) = 2 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn2)
  simp only [rho, ite_eq_right hn2]
  rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) / 2)]
  have he : 2 / ((n : ℝ) - 2) * (1 - (n : ℝ) / 2) = -1 := by
    field_simp
    ring
  rw [he, Real.rpow_neg_one]
  field_simp

/-- The heat root equation initially decreases from its zero at the origin. -/
theorem one_add_two_div_lt_rho (n : ℕ) (hn : 1 ≤ n) : 1 + 2 / (n : ℝ) < rho n := by
  rcases eq_or_lt_of_le hn with hn | hn
  · subst n
    norm_num [rho_one]
  · by_cases hn2 : n = 2
    · subst n
      simpa [rho_two] using Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    · have hn3 : 3 ≤ n := by omega
      have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have hn0 : (0 : ℝ) < n := by linarith
      have hbase : 0 < (n : ℝ) / 2 := by positivity
      have hlog : 1 - 2 / (n : ℝ) ≤ Real.log ((n : ℝ) / 2) := by
        simpa only [inv_div] using Real.one_sub_inv_le_log_of_pos hbase
      have ht : 2 / (n : ℝ) ≤ Real.log ((n : ℝ) / 2) * (2 / ((n : ℝ) - 2)) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ (by linarith : (0 : ℝ) < n - 2)).mpr
        have he : 2 / (n : ℝ) * ((n : ℝ) - 2) = 2 * (1 - 2 / (n : ℝ)) := by
          field_simp
        rw [he]
        nlinarith
      rw [rho, ite_eq_right hn2, Real.rpow_def_of_pos hbase]
      have hexp : 1 + 2 / (n : ℝ) < Real.exp (2 / (n : ℝ)) := by
        simpa [add_comm] using Real.add_one_lt_exp (by positivity : 2 / (n : ℝ) ≠ 0)
      exact hexp.trans_le (Real.exp_le_exp.mpr ht)

/-- An exponential curve meets an affine line through `(0, 1)` at at most one positive point. -/
theorem eq_of_exp_affine_eq {c d x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hex : Real.exp (-c * x) = 1 - d * x)
    (hey : Real.exp (-c * y) = 1 - d * y) : x = y := by
  wlog hxy : x < y generalizing x y
  · rcases lt_trichotomy x y with h | h | h
    · exact this hx hy hex hey h
    · exact h
    · exact (this hy hx hey hex h).symm
  have hcx : -c * x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc.ne') hx.ne'
  have hcy : -c * y ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc.ne') hy.ne'
  have h := strictConvexOn_exp.secant_strict_mono
    (a := 0) (x := -c * y) (y := -c * x) (by simp) (by simp) (by simp)
    hcy hcx (by nlinarith)
  simp only [Real.exp_zero, sub_zero, hex, hey] at h
  have h₁ : (1 - d * y - 1) / (-c * y) = d / c := by
    field_simp
    ring
  have h₂ : (1 - d * x - 1) / (-c * x) = d / c := by
    field_simp
    ring
  rw [h₁, h₂] at h
  exact (lt_irrefl _ h).elim

/-- Opposite endpoint signs locate the unique positive exponential-affine intersection. -/
theorem existsUnique_exp_affine_eq_of_signs {c d l r : ℝ} (hc : 0 < c)
    (hl : 0 < l) (hlr : l < r)
    (hlneg : Real.exp (-c * l) < 1 - d * l)
    (hrpos : 1 - d * r < Real.exp (-c * r)) :
    ∃! a : ℝ, a ∈ Ioo l r ∧ Real.exp (-c * a) = 1 - d * a := by
  let F : ℝ → ℝ := fun a ↦ Real.exp (-c * a) - (1 - d * a)
  have hF : Continuous F := by fun_prop
  obtain ⟨a, ha, he⟩ := intermediate_value_Ioo hlr.le hF.continuousOn
    (show 0 ∈ Ioo (F l) (F r) by constructor <;> dsimp [F] <;> linarith)
  have heq : Real.exp (-c * a) = 1 - d * a := sub_eq_zero.mp he
  refine ⟨a, ⟨ha, heq⟩, fun b hb ↦ ?_⟩
  exact eq_of_exp_affine_eq hc (hl.trans hb.1.1) (hl.trans ha.1) hb.2 heq

private theorem exists_neg_of_hasDerivAt_neg {F : ℝ → ℝ} {D R : ℝ}
    (hF : HasDerivAt F D 0) (hF0 : F 0 = 0) (hD : D < 0) (hR : 0 < R) :
    ∃ a ∈ Ioo 0 R, F a < 0 := by
  have hneg : ∀ᶠ a in 𝓝 (0 : ℝ),
      Function.update (fun x ↦ (F x - F 0) / (x - 0)) 0 D a < 0 :=
    hF.continuousAt_div.tendsto.eventually (by simpa using eventually_lt_nhds hD)
  have hneg' := hneg.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  have hsmall : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  obtain ⟨a, ha, haR, haneg⟩ := (hpos.and (hsmall.and hneg')).exists
  rw [Function.update_of_ne ha.ne', hF0, sub_zero, sub_zero] at haneg
  exact ⟨a, ⟨ha, haR⟩, by simpa using (div_lt_iff₀ ha).mp haneg⟩

/-- If the exponential initially falls faster than the affine line, their positive
intersection exists and lies before the affine line becomes zero. -/
theorem existsUnique_exp_affine_eq {c d : ℝ} (hd : 0 < d) (hdc : d < c) :
    ∃! a : ℝ, a ∈ Ioo 0 d⁻¹ ∧ Real.exp (-c * a) = 1 - d * a := by
  let F : ℝ → ℝ := fun a ↦ Real.exp (-c * a) - (1 - d * a)
  have hderiv : HasDerivAt F (d - c) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (-c)).exp).sub
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).const_mul d))
      using 1
    · ext a
      simp [F]
    · simp
      ring
  obtain ⟨l, hl, hlneg⟩ := exists_neg_of_hasDerivAt_neg hderiv (by simp [F])
    (by linarith) (inv_pos.mpr hd)
  obtain ⟨a, ha, -⟩ := existsUnique_exp_affine_eq_of_signs (d := d) (hd.trans hdc) hl.1 hl.2
    (by dsimp [F] at hlneg; linarith)
    (by simp [hd.ne', Real.exp_pos])
  exact ⟨a, ⟨⟨hl.1.trans ha.1.1, ha.1.2⟩, ha.2⟩,
    fun b hb ↦ eq_of_exp_affine_eq (hd.trans hdc) hb.1.1 (hl.1.trans ha.1.1) hb.2 ha.2⟩

/-- In every positive dimension the heat tangency equation has exactly one positive root
before `n / 2`. -/
theorem existsUnique_heatRoot_positive (n : ℕ) (hn : 1 ≤ n) :
    ∃! a : ℝ, a ∈ Ioo 0 ((n : ℝ) / 2) ∧
      Real.exp (-(rho n - 1) * a) = 1 - 2 * a / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd : 0 < 2 / (n : ℝ) := by positivity
  have hdc : 2 / (n : ℝ) < rho n - 1 := by linarith [one_add_two_div_lt_rho n hn]
  simpa only [inv_div, div_mul_eq_mul_div] using existsUnique_exp_affine_eq hd hdc

/-- The one-dimensional Poisson equation has the exact tangency parameter `1 / 5`. -/
theorem existsUnique_poissonRoot_one :
    ∃! a : ℝ, a ∈ Ioo (1 / 12) (1 / 3) ∧
      (1 - a) / (1 + a) ^ 2 = 1 / (1 + 4 * a) := by
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro a ha
  have ha0 : 0 < a := by linarith [ha.1.1]
  have h₁ : 1 + a ≠ 0 := by positivity
  have h₂ : 1 + 4 * a ≠ 0 := by positivity
  have he := ha.2
  field_simp at he
  have hf : a * (1 - 5 * a) = 0 := by nlinarith
  have h := (mul_eq_zero.mp hf).resolve_left ha0.ne'
  linarith

end PartialBalayage.Constants
