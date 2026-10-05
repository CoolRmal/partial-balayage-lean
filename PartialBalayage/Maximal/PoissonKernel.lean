/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupDefinitions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Normalization of the genuine Poisson kernel

A Laplace--Gamma representation expresses the exact Poisson kernel as a positive Gaussian
mixture. The Gaussian integral reduces the product integral to the Euler integral for
`Γ(1/2)`. Product integrability and total mass one follow without a normalization hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage

/-- The positive Laplace--Gaussian integrand representing the Poisson kernel. -/
def poissonLaplaceIntegrand (n : ℕ) (t u : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  u ^ (((n : ℝ) + 1) / 2 - 1) * Real.exp (-(t ^ 2 * u)) * Real.exp (-u * ‖x‖ ^ 2)

private theorem integrable_poissonGaussian (n : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ Real.exp (-u * ‖x‖ ^ 2)) := by
  by_contra h
  have hmass := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin n)) hu
  rw [integral_undef h] at hmass
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos hu) _).ne' hmass.symm

/-- Gaussian integration of the Laplace integrand leaves the dimension-free half-Gamma power. -/
theorem integral_poissonLaplaceIntegrand_space (n : ℕ) (t : ℝ) {u : ℝ} (hu : 0 < u) :
    (∫ x : EuclideanSpace ℝ (Fin n), poissonLaplaceIntegrand n t u x) =
      Real.pi ^ ((n : ℝ) / 2) * u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u)) := by
  unfold poissonLaplaceIntegrand
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hu]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [Real.div_rpow Real.pi_nonneg hu.le,
    div_eq_mul_inv (Real.pi ^ ((n : ℝ) / 2)) (u ^ ((n : ℝ) / 2)),
    ← Real.rpow_neg hu.le]
  calc
    _ = Real.pi ^ ((n : ℝ) / 2) *
        (u ^ (((n : ℝ) + 1) / 2 - 1) * u ^ (-((n : ℝ) / 2))) *
        Real.exp (-(t ^ 2 * u)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hu]
      rw [show ((n : ℝ) + 1) / 2 - 1 + -((n : ℝ) / 2) = -(1 / 2 : ℝ) by ring]

private theorem integrable_poissonGammaHalf {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ ↦ u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2 : ℝ)) (p := 1) (b := t ^ 2)
      (by norm_num) (by norm_num) (by positivity))

/-- The Laplace--Gaussian representation is genuinely integrable on the product space. -/
theorem integrable_poissonLaplaceIntegrand (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (Function.uncurry (poissonLaplaceIntegrand n t))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry (poissonLaplaceIntegrand n t))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    change AEStronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) ↦
      p.1 ^ (((n : ℝ) + 1) / 2 - 1) * Real.exp (-(t ^ 2 * p.1)) *
        Real.exp (-p.1 * ‖p.2‖ ^ 2)) _
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (integrable_poissonGaussian n hu).const_mul
      (u ^ (((n : ℝ) + 1) / 2 - 1) * Real.exp (-(t ^ 2 * u)))
  · apply ((integrable_poissonGammaHalf ht).const_mul (Real.pi ^ ((n : ℝ) / 2))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    have hnorm : (fun x : EuclideanSpace ℝ (Fin n) ↦
        ‖poissonLaplaceIntegrand n t u x‖) = poissonLaplaceIntegrand n t u := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold poissonLaplaceIntegrand
      positivity
    change Real.pi ^ ((n : ℝ) / 2) *
      (u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u))) =
      ∫ x : EuclideanSpace ℝ (Fin n), ‖poissonLaplaceIntegrand n t u x‖
    rw [hnorm, integral_poissonLaplaceIntegrand_space n t hu]
    ring

/-- The exact Poisson kernel equals its positive Laplace--Gaussian integral representation. -/
theorem poissonKernel_eq_laplace_integral (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    poissonKernel n t x = t / Real.pi ^ (((n : ℝ) + 1) / 2) *
      ∫ u in Ioi (0 : ℝ), poissonLaplaceIntegrand n t u x := by
  have hb : 0 < t ^ 2 + ‖x‖ ^ 2 := by positivity
  have heq : (fun u : ℝ ↦ poissonLaplaceIntegrand n t u x) =
      fun u ↦ u ^ (((n : ℝ) + 1) / 2 - 1) *
        Real.exp (-((t ^ 2 + ‖x‖ ^ 2) * u)) := by
    funext u
    unfold poissonLaplaceIntegrand
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [heq, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hb,
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hb.le, Real.one_rpow]
  unfold poissonKernel
  ring

/-- The product integral of the raw positive Gaussian mixture has its exact Gamma mass. -/
theorem integral_poissonLaplaceIntegrand (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ u in Ioi (0 : ℝ), ∫ x : EuclideanSpace ℝ (Fin n),
      poissonLaplaceIntegrand n t u x) = Real.pi ^ (((n : ℝ) + 1) / 2) / t := by
  have heq : (∫ u in Ioi (0 : ℝ), ∫ x : EuclideanSpace ℝ (Fin n),
      poissonLaplaceIntegrand n t u x) =
      ∫ u in Ioi (0 : ℝ), Real.pi ^ ((n : ℝ) / 2) *
        (u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (∫ x : EuclideanSpace ℝ (Fin n), poissonLaplaceIntegrand n t u x) =
      Real.pi ^ ((n : ℝ) / 2) * (u ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 * u)))
    rw [integral_poissonLaplaceIntegrand_space n t hu]
    ring
  rw [heq, integral_const_mul, show -(1 / 2 : ℝ) = (1 / 2 : ℝ) - 1 by norm_num,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by positivity),
    Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, Real.sqrt_sq ht.le,
    Real.sqrt_eq_rpow]
  calc
    _ = (Real.pi ^ ((n : ℝ) / 2) * Real.pi ^ (1 / 2 : ℝ)) / t := by ring
    _ = _ := by
      rw [← Real.rpow_add Real.pi_pos,
        show (n : ℝ) / 2 + (1 / 2 : ℝ) = ((n : ℝ) + 1) / 2 by ring]

/-- The exact Poisson kernel is integrable at every positive height in every dimension. -/
theorem integrable_poissonKernel (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (poissonKernel n t) := by
  apply ((integrable_poissonLaplaceIntegrand n ht).integral_prod_right.const_mul
    (t / Real.pi ^ (((n : ℝ) + 1) / 2))).congr
  exact Eventually.of_forall (fun x ↦ (poissonKernel_eq_laplace_integral n ht x).symm)

/-- The genuine Poisson kernel has total mass one, with no normalization premise. -/
theorem integral_poissonKernel (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin n), poissonKernel n t x) = 1 := by
  conv_lhs => enter [2, x]; rw [poissonKernel_eq_laplace_integral n ht x]
  rw [integral_const_mul, ← integral_integral_swap (integrable_poissonLaplaceIntegrand n ht),
    integral_poissonLaplaceIntegrand n ht]
  field_simp [(Real.rpow_pos_of_pos Real.pi_pos (((n : ℝ) + 1) / 2)).ne', ht.ne']

/-- The Poisson kernel defines an actual measure by its nonnegative density. -/
def poissonKernelMeasure (n : ℕ) (t : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (poissonKernel n t x))

/-- The nonnegative Poisson kernel also has total mass one as a Lebesgue integral. -/
theorem lintegral_poissonKernel (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (poissonKernel n t x)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernel n ht)
    (Eventually.of_forall (fun x ↦ (poissonKernel_pos n ht x).le)),
    integral_poissonKernel n ht, ENNReal.ofReal_one]

/-- At every positive height, the actual Poisson density measure is a probability measure. -/
theorem isProbabilityMeasure_poissonKernelMeasure (n : ℕ) {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (poissonKernelMeasure n t) := by
  constructor
  rw [poissonKernelMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_poissonKernel n ht]

end PartialBalayage
