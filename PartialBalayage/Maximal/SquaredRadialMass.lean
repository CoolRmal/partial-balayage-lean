/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic

/-!
# Euclidean mass of profiles in the squared radius

Polar integration and the substitution `z = r²` give the exact radial Jacobian. The Gaussian
integral and Euler's Gamma integral determine its normalization in every positive dimension.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage

private theorem radial_square_power (n : ℕ) (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    (r ^ 2) ^ ((n : ℝ) / 2 - 1) * r = r ^ (n - 1) := by
  calc
    _ = r ^ (2 * ((n : ℝ) / 2 - 1)) * r ^ (1 : ℝ) := by
      rw [← Real.rpow_two r, ← Real.rpow_mul hr.le, Real.rpow_one]
    _ = r ^ (2 * ((n : ℝ) / 2 - 1) + 1) := (Real.rpow_add hr _ _).symm
    _ = _ := by
      rw [← Real.rpow_natCast]
      congr 1
      rw [Nat.cast_sub hn]
      push_cast
      ring

private theorem radial_square_substitution (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f (r ^ 2)) =
      (1 / 2 : ℝ) * ∫ z in Ioi (0 : ℝ), f z * z ^ ((n : ℝ) / 2 - 1) := by
  have hs := integral_comp_rpow_Ioi_of_pos
    (g := fun z ↦ f z * z ^ ((n : ℝ) / 2 - 1)) (p := 2) (by norm_num)
  have heq : (∫ r in Ioi (0 : ℝ),
      (2 * r ^ (2 - 1 : ℝ)) • (f (r ^ (2 : ℝ)) *
        (r ^ (2 : ℝ)) ^ ((n : ℝ) / 2 - 1))) =
      2 * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f (r ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [show (2 - 1 : ℝ) = 1 by norm_num, Real.rpow_one,
      Real.rpow_two, smul_eq_mul]
    rw [show 2 * r * (f (r ^ 2) * (r ^ 2) ^ ((n : ℝ) / 2 - 1)) =
      2 * ((r ^ 2) ^ ((n : ℝ) / 2 - 1) * r) * f (r ^ 2) by ring,
      radial_square_power n hn hr]
    ring
  rw [heq] at hs
  linarith

private theorem integral_radial_square_polar (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n), f (‖x‖ ^ 2)) =
      ((n : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2) *
        ∫ z in Ioi (0 : ℝ), f z * z ^ ((n : ℝ) / 2 - 1) := by
  have : NeZero n := ⟨by omega⟩
  rw [integral_fun_norm_addHaar volume (fun r ↦ f (r ^ 2))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
  rw [radial_square_substitution n hn f]
  ring

/-- Polar integration in the squared radius, with its exact Gamma normalization. -/
theorem integral_radial_square (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n), f (‖x‖ ^ 2)) =
      (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
        ∫ z in Ioi (0 : ℝ), f z * z ^ ((n : ℝ) / 2 - 1) := by
  have hβ : 0 < (n : ℝ) / 2 := div_pos
    (by exact_mod_cast (show 0 < n by omega)) (by norm_num)
  have hΓ := Real.Gamma_pos_of_pos hβ
  have heuler : (∫ z in Ioi (0 : ℝ), Real.exp (-z) *
      z ^ ((n : ℝ) / 2 - 1)) = Real.Gamma ((n : ℝ) / 2) :=
    (Real.Gamma_eq_integral hβ).symm
  have hgauss : (∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(‖x‖ ^ 2))) =
      Real.pi ^ ((n : ℝ) / 2) := by
    simpa only [neg_one_mul, div_one, finrank_euclideanSpace, Fintype.card_fin] using
      (GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := EuclideanSpace ℝ (Fin n)) (by norm_num : 0 < (1 : ℝ)))
  rw [integral_radial_square_polar n hn (fun z ↦ Real.exp (-z)), heuler] at hgauss
  have hc := (eq_div_iff hΓ.ne').mpr hgauss
  rw [integral_radial_square_polar n hn f, hc]

/-- An integrable profile with the radial Gamma weight gives an integrable Euclidean kernel. -/
theorem integrable_radial_square (n : ℕ) (hn : 1 ≤ n) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun z ↦ f z * z ^ ((n : ℝ) / 2 - 1)) (Ioi 0)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ f (‖x‖ ^ 2)) := by
  have : NeZero n := ⟨by omega⟩
  apply (integrable_fun_norm_addHaar volume (f := fun r ↦ f (r ^ 2))).mpr
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hi := (integrableOn_Ioi_comp_rpow_iff'
    (fun z ↦ f z * z ^ ((n : ℝ) / 2 - 1)) (p := 2) (by norm_num)).mpr hf
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [show (2 - 1 : ℝ) = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, smul_eq_mul]
  rw [show r * (f (r ^ 2) * (r ^ 2) ^ ((n : ℝ) / 2 - 1)) =
    ((r ^ 2) ^ ((n : ℝ) / 2 - 1) * r) * f (r ^ 2) by ring,
    radial_square_power n hn hr]

private theorem radial_square_scale_eq (n : ℕ) (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin n)) :
    f ((‖x‖ / R) ^ 2) = f (‖R⁻¹ • x‖ ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), div_eq_mul_inv]
  congr 2
  ring

/-- The Euclidean kernel stays integrable under every positive radial dilation. -/
theorem integrable_scaled_radial_square (n : ℕ) (hn : 1 ≤ n) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun z ↦ f z * z ^ ((n : ℝ) / 2 - 1)) (Ioi 0))
    {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ f ((‖x‖ / R) ^ 2)) := by
  apply ((integrable_radial_square n hn hf).comp_smul (inv_ne_zero hR.ne')).congr
  exact Eventually.of_forall (fun x ↦ (radial_square_scale_eq n f hR x).symm)

/-- The exact ambient mass of a positive radial dilation of a squared-radius profile. -/
theorem integral_scaled_radial_square (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : EuclideanSpace ℝ (Fin n), f ((‖x‖ / R) ^ 2)) =
      R ^ n * (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
        ∫ z in Ioi (0 : ℝ), f z * z ^ ((n : ℝ) / 2 - 1) := by
  have heq : (fun x : EuclideanSpace ℝ (Fin n) ↦ f ((‖x‖ / R) ^ 2)) =
      fun x ↦ f (‖R⁻¹ • x‖ ^ 2) := funext (radial_square_scale_eq n f hR)
  rw [heq, Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
    (fun x : EuclideanSpace ℝ (Fin n) ↦ f (‖x‖ ^ 2)) hR.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [integral_radial_square n hn f]
  ring

end PartialBalayage
