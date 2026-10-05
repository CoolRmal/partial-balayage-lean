/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonSubordination
public import PartialBalayage.Maximal.PoissonKato
public import Mathlib.Analysis.Fourier.Convolution

/-!
# The genuine isotropic Poisson Fourier multiplier

The normalized spatial Poisson kernel is identified by its ordinary Fourier integral,
using the genuine integrable Laplace--Gaussian representation and exact subordination.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set Filter
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

/-- The ordinary Fourier transform of the real Gaussian, viewed as a complex input. -/
theorem fourier_real_gaussian {u : ℝ} (hu : 0 < u) (ξ : X) :
    𝓕 (fun x : X ↦ (Real.exp (-u * ‖x‖ ^ 2) : ℂ)) ξ =
      (((Real.pi / u) ^ ((n : ℝ) / 2) *
        Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / u))) : ℝ) := by
  have h := fourier_gaussian_innerProductSpace
    (V := X) (b := (u : ℂ)) (by simpa using hu) ξ
  have heq : (fun x : X ↦ (Real.exp (-u * ‖x‖ ^ 2) : ℂ)) =
      fun x : X ↦ Complex.exp (-(u : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow]
  rw [heq, h]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← Complex.ofReal_div,
    show (n : ℂ) / 2 = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (div_nonneg Real.pi_nonneg hu.le)]
  push_cast
  simp only [neg_mul, neg_div]

/-- Gaussian Fourier integration of a slice of the genuine Poisson mixture. -/
theorem integral_poissonLaplace_phase_space (t : ℝ) {u : ℝ} (hu : 0 < u) (ξ : X) :
    (∫ x : X, Complex.exp ((-2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
      (PartialBalayage.poissonLaplaceIntegrand n t u x : ℂ)) =
      ((Real.pi ^ ((n : ℝ) / 2) * u ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(t ^ 2 * u + (Real.pi * ‖ξ‖) ^ 2 / u))) : ℝ) := by
  let A : ℝ := u ^ (((n : ℝ) + 1) / 2 - 1) * Real.exp (-(t ^ 2 * u))
  have hfactor : (∫ x : X, Complex.exp ((-2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
      (PartialBalayage.poissonLaplaceIntegrand n t u x : ℂ)) =
      (A : ℂ) * 𝓕 (fun x : X ↦ (Real.exp (-u * ‖x‖ ^ 2) : ℂ)) ξ := by
    rw [Real.fourier_eq', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    change _ = (A : ℂ) *
      (Complex.exp ((-2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
        (Real.exp (-u * ‖x‖ ^ 2) : ℂ))
    dsimp [A, PartialBalayage.poissonLaplaceIntegrand]
    push_cast
    ring
  have hscalar : A * (Real.pi / u) ^ ((n : ℝ) / 2) =
      Real.pi ^ ((n : ℝ) / 2) * u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u)) := by
    calc
      _ = ∫ x : X, PartialBalayage.poissonLaplaceIntegrand n t u x := by
        unfold PartialBalayage.poissonLaplaceIntegrand
        rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hu]
        simp only [finrank_euclideanSpace, Fintype.card_fin]
        rfl
      _ = _ := PartialBalayage.integral_poissonLaplaceIntegrand_space n t hu
  rw [hfactor, fourier_real_gaussian hu]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc, hscalar, mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

/-- A fixed Fourier phase preserves the actual product integrability of the Gaussian mixture. -/
theorem integrable_poissonLaplace_phase {t : ℝ} (ht : 0 < t) (ξ : X) :
    Integrable (fun p : ℝ × X ↦
      Complex.exp ((-2 * Real.pi * ⟪p.2, ξ⟫ : ℝ) * Complex.I) *
        (PartialBalayage.poissonLaplaceIntegrand n t p.1 p.2 : ℂ))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hbase := Complex.ofRealCLM.integrable_comp
    (PartialBalayage.integrable_poissonLaplaceIntegrand n ht)
  apply hbase.bdd_mul (by fun_prop) (c := 1)
  filter_upwards with p
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The full ordinary Fourier integral of the genuine Gaussian mixture is evaluated exactly. -/
theorem integral_poissonLaplace_phase {t : ℝ} (ht : 0 < t) (ξ : X) :
    (∫ u in Ioi (0 : ℝ), ∫ x : X,
      Complex.exp ((-2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
        (PartialBalayage.poissonLaplaceIntegrand n t u x : ℂ)) =
      ((Real.pi ^ (((n : ℝ) + 1) / 2) / t *
        Real.exp (-(2 * Real.pi * t * ‖ξ‖))) : ℝ) := by
  have heq : (∫ u in Ioi (0 : ℝ), ∫ x : X,
      Complex.exp ((-2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
        (PartialBalayage.poissonLaplaceIntegrand n t u x : ℂ)) =
      ∫ u in Ioi (0 : ℝ), (((Real.pi ^ ((n : ℝ) / 2) * u ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(t ^ 2 * u + (Real.pi * ‖ξ‖) ^ 2 / u))) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact integral_poissonLaplace_phase_space t hu ξ
  rw [heq, integral_complex_ofReal]
  congr 1
  have hfactor : (∫ u in Ioi (0 : ℝ), Real.pi ^ ((n : ℝ) / 2) *
      u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u + (Real.pi * ‖ξ‖) ^ 2 / u))) =
      Real.pi ^ ((n : ℝ) / 2) * ∫ u in Ioi (0 : ℝ),
        u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u + (Real.pi * ‖ξ‖) ^ 2 / u)) := by
    simp only [mul_assoc, integral_const_mul]
  rw [hfactor, integral_poisson_subordination ht (by positivity)]
  have hpi : Real.pi ^ ((n : ℝ) / 2) * Real.sqrt Real.pi =
      Real.pi ^ (((n : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  rw [show 2 * t * (Real.pi * ‖ξ‖) = 2 * Real.pi * t * ‖ξ‖ by ring]
  calc
    _ = (Real.pi ^ ((n : ℝ) / 2) * Real.sqrt Real.pi) / t *
        Real.exp (-(2 * Real.pi * t * ‖ξ‖)) := by ring
    _ = _ := by rw [hpi]

/-- Fourier transformation of the actual normalized spatial Poisson kernel. -/
theorem fourier_poissonKernel {t : ℝ} (ht : 0 < t) (ξ : X) :
    𝓕 (fun x : X ↦ (PartialBalayage.poissonKernel n t x : ℂ)) ξ =
      (Real.exp (-(2 * Real.pi * t * ‖ξ‖)) : ℂ) := by
  let c : ℝ := t / Real.pi ^ (((n : ℝ) + 1) / 2)
  have hrepr : 𝓕 (fun x : X ↦ (PartialBalayage.poissonKernel n t x : ℂ)) ξ =
      (c : ℂ) * ∫ x : X, ∫ u in Ioi (0 : ℝ),
        Complex.exp ((-2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
          (PartialBalayage.poissonLaplaceIntegrand n t u x : ℂ) := by
    rw [Real.fourier_eq', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [PartialBalayage.poissonKernel_eq_laplace_integral n ht x]
    simp only [Complex.ofReal_mul, smul_eq_mul]
    rw [integral_const_mul, integral_complex_ofReal]
    dsimp [c]
    ring
  rw [hrepr, ← integral_integral_swap (integrable_poissonLaplace_phase ht ξ),
    integral_poissonLaplace_phase ht ξ, ← Complex.ofReal_mul]
  congr 1
  dsimp [c]
  have hp : Real.pi ^ (((n : ℝ) + 1) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  field_simp [hp, ht.ne']

end PartialBalayage.Linear
