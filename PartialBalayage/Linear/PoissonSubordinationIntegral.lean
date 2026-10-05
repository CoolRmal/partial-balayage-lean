/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The exact scalar Gaussian subordination integral

The change of variable `x ↦ x - b / x` maps the positive half-line onto the real line.
Reciprocal symmetry splits its Gaussian Jacobian into two equal integrals. This supplies
the exact scalar integral needed to identify the genuine Poisson Fourier multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Linear

/-- Positive reciprocal substitution, including its actual absolute Jacobian. -/
theorem integral_Ioi_reciprocal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), (b / x ^ 2) • g (b / x)) = ∫ y in Ioi (0 : ℝ), g y := by
  have himage : (fun x : ℝ ↦ b / x) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos hb hx
    · intro hy
      refine ⟨b / y, div_pos hb hy, ?_⟩
      field_simp
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z : ℝ ↦ b / z) (-b / x ^ 2) (Ioi 0) x := by
    intro x hx
    simpa only [Pi.div_apply, id_eq, zero_mul, mul_one, zero_sub] using
      ((hasDerivAt_const x b).fun_div (hasDerivAt_id x) hx.ne').hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ ↦ b / x) (Ioi 0) := by
    intro x hx y hy hxy
    have heq := (div_eq_div_iff hx.ne' hy.ne').mp hxy
    nlinarith
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [himage] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change (b / x ^ 2) • g (b / x) = |-b / x ^ 2| • g (b / x)
  rw [neg_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ b / x ^ 2)]

/-- Reciprocal substitution also preserves actual integrability with its Jacobian. -/
theorem integrableOn_Ioi_reciprocal_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x ↦ (b / x ^ 2) • g (b / x)) (Ioi (0 : ℝ)) ↔
      IntegrableOn g (Ioi (0 : ℝ)) := by
  have himage : (fun x : ℝ ↦ b / x) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos hb hx
    · intro hy
      refine ⟨b / y, div_pos hb hy, ?_⟩
      field_simp
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z : ℝ ↦ b / z) (-b / x ^ 2) (Ioi 0) x := by
    intro x hx
    simpa only [Pi.div_apply, id_eq, zero_mul, mul_one, zero_sub] using
      ((hasDerivAt_const x b).fun_div (hasDerivAt_id x) hx.ne').hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ ↦ b / x) (Ioi 0) := by
    intro x hx y hy hxy
    have heq := (div_eq_div_iff hx.ne' hy.ne').mp hxy
    nlinarith
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv hinj g
  rw [himage] at h
  rw [h]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro x hx
  change (b / x ^ 2) • g (b / x) = |-b / x ^ 2| • g (b / x)
  rw [neg_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ b / x ^ 2)]

/-- The positive Gaussian shift map has the entire real line as its image. -/
theorem image_sub_reciprocal_Ioi {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ ↦ x - b / x) '' Ioi 0 = univ := by
  apply eq_univ_of_forall
  intro y
  let x := (y + Real.sqrt (y ^ 2 + 4 * b)) / 2
  have hs : y ^ 2 < y ^ 2 + 4 * b := by linarith
  have habs : |y| < Real.sqrt (y ^ 2 + 4 * b) := by
    simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_lt_sqrt (sq_nonneg y) hs
  have hx : 0 < x := by
    dsimp [x]
    have hy := neg_abs_le y
    linarith
  refine ⟨x, hx, ?_⟩
  have hsqr := Real.sq_sqrt (by positivity : 0 ≤ y ^ 2 + 4 * b)
  change x - b / x = y
  field_simp [hx.ne']
  dsimp [x]
  nlinarith

/-- The Gaussian shift map is injective on the positive half-line. -/
theorem injOn_sub_reciprocal_Ioi {b : ℝ} (hb : 0 < b) :
    InjOn (fun x : ℝ ↦ x - b / x) (Ioi 0) := by
  apply StrictMonoOn.injOn
  intro x hx y hy hxy
  have hdiv : b / y < b / x := div_lt_div_of_pos_left hb hx hxy
  linarith

/-- The shifted Gaussian is genuinely integrable on the positive half-line. -/
theorem integrableOn_exp_sub_reciprocal_sq (b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-((x - b / x) ^ 2))) (Ioi 0) := by
  have hbase := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
    (s := Ioi (0 : ℝ))
  apply (hbase.const_mul (Real.exp (2 * b))).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : (x - b / x) ^ 2 = x ^ 2 - 2 * b + (b / x) ^ 2 := by
    field_simp [hx.ne']
    ring
  rw [heq]
  nlinarith [sq_nonneg (b / x)]

/-- The genuine derivative of the Gaussian shift map on the positive half-line. -/
theorem hasDerivAt_sub_reciprocal (b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ ↦ z - b / z) (1 + b / x ^ 2) x := by
  simpa only [Pi.div_apply, Pi.sub_apply, id_eq, zero_mul, mul_one, zero_sub, neg_div,
    sub_neg_eq_add] using ((hasDerivAt_id x).fun_sub
      ((hasDerivAt_const x b).fun_div (hasDerivAt_id x) hx))

/-- Reciprocal symmetry gives the exact Gaussian shift integral. -/
theorem integral_exp_sub_reciprocal_sq {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-((x - b / x) ^ 2))) = Real.sqrt Real.pi / 2 := by
  let g : ℝ → ℝ := fun x ↦ Real.exp (-((x - b / x) ^ 2))
  have hg := integrableOn_exp_sub_reciprocal_sq b
  have hsym : ∀ x ∈ Ioi (0 : ℝ), g (b / x) = g x := by
    intro x hx
    dsimp [g]
    congr 2
    have heq : b / x - b / (b / x) = -(x - b / x) := by
      field_simp
      ring
    rw [heq, neg_sq]
  have hrec : (∫ x in Ioi (0 : ℝ), b / x ^ 2 * g x) = ∫ x in Ioi (0 : ℝ), g x := by
    convert integral_Ioi_reciprocal g hb using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change b / x ^ 2 * g x = (b / x ^ 2) • g (b / x)
    rw [hsym x hx]
    rfl
  have hrecint : IntegrableOn (fun x ↦ b / x ^ 2 * g x) (Ioi (0 : ℝ)) := by
    apply ((integrableOn_Ioi_reciprocal_iff g hb).mpr hg).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [hsym x hx]
    rfl
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx ↦ (hasDerivAt_sub_reciprocal b hx.ne').hasDerivWithinAt)
    (injOn_sub_reciprocal_Ioi hb) (fun y : ℝ ↦ Real.exp (-(y ^ 2)))
  rw [image_sub_reciprocal_Ioi hb, setIntegral_univ] at hchange
  have hsplit : (∫ x in Ioi (0 : ℝ), |1 + b / x ^ 2| •
      Real.exp (-((x - b / x) ^ 2))) = 2 * ∫ x in Ioi (0 : ℝ), g x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), g x + b / x ^ 2 * g x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change |1 + b / x ^ 2| • Real.exp (-((x - b / x) ^ 2)) =
          g x + b / x ^ 2 * g x
        rw [abs_of_nonneg (by positivity : 0 ≤ 1 + b / x ^ 2)]
        simp only [smul_eq_mul]
        dsimp [g]
        ring
      _ = _ := by rw [integral_add hg hrecint, hrec]; ring
  rw [hsplit] at hchange
  have hgauss : (∫ x : ℝ, Real.exp (-(x ^ 2))) = Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  rw [hgauss] at hchange
  change (∫ x in Ioi (0 : ℝ), g x) = _
  linarith

/-- The scalar subordination Gaussian is an integrable ordinary function. -/
theorem integrableOn_exp_sq_add_reciprocal_sq (b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-(x ^ 2 + (b / x) ^ 2))) (Ioi 0) := by
  apply ((integrableOn_exp_sub_reciprocal_sq b).const_mul (Real.exp (-(2 * b)))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [← Real.exp_add]
  congr 1
  field_simp [hx.ne']
  ring

/-- The reciprocal Gaussian integral has its exact exponential evaluation. -/
theorem integral_exp_sq_add_reciprocal_sq {b : ℝ} (hb : 0 ≤ b) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(x ^ 2 + (b / x) ^ 2))) =
      Real.sqrt Real.pi / 2 * Real.exp (-(2 * b)) := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa using integral_gaussian_Ioi (1 : ℝ)
  have heq : (∫ x in Ioi (0 : ℝ), Real.exp (-(x ^ 2 + (b / x) ^ 2))) =
      Real.exp (-(2 * b)) * ∫ x in Ioi (0 : ℝ), Real.exp (-((x - b / x) ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change Real.exp (-(x ^ 2 + (b / x) ^ 2)) =
      Real.exp (-(2 * b)) * Real.exp (-((x - b / x) ^ 2))
    rw [← Real.exp_add]
    congr 1
    field_simp [hx.ne']
    ring
  rw [heq, integral_exp_sub_reciprocal_sq hb]
  ring

end PartialBalayage.Linear
