/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonSelfAdjoint
public import PartialBalayage.Linear.PoissonGeneratorScalar
public import PartialBalayage.Linear.IsotropicEnergySpace
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Actual Poisson quadratic defects and isotropic half-order energy

Plancherel gives the positive spectral formula for genuine spatial Poisson quadratic
defects. Fatou and the pointwise upper bound give their full extended limit, including
inputs with infinite isotropic energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance poissonQuadraticRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonQuadraticScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)

/-- The actual positive-height spatial Poisson quadratic defect. -/
def poissonQuadraticDefect {t : ℝ} (ht : 0 < t) (f : L²) : ℝ :=
  (inner ℂ f (poissonQuotientL2 ht f)).re

/-- Every actual Poisson quotient has its exact full isotropic Fourier symbol. -/
theorem fourier_poissonQuotientL2_ae {t : ℝ} (ht : 0 < t) (f : L²) :
    ∀ᵐ ξ, (𝓕 (poissonQuotientL2 ht f) : L²) ξ =
      (poissonRate t (2 * Real.pi * ‖ξ‖) : ℂ) • (𝓕 f : L²) ξ := by
  have hsubF (a b : L²) : 𝓕 (a - b) = 𝓕 a - 𝓕 b :=
    (Lp.fourierTransformₗᵢ D E).map_sub a b
  rw [poissonQuotientL2, fourier_smul, hsubF, fourier_poissonConvolutionL2 ht]
  filter_upwards [Lp.coeFn_smul (t⁻¹ : ℂ)
    (𝓕 f - multiplyOperatorL2 (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f)),
    Lp.coeFn_sub (𝓕 f) (multiplyOperatorL2 (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f)),
    multiplyOperatorL2_ae (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 f)] with ξ hs hd hm
  rw [hs, Pi.smul_apply, hd, Pi.sub_apply, hm]
  change (t⁻¹ : ℂ) • ((𝓕 f : L²) ξ -
    (Real.exp (-(2 * Real.pi * t * ‖ξ‖)) : ℂ) • (𝓕 f : L²) ξ) = _
  have hid (c : ℂ) (v : E) : v - c • v = (1 - c) • v := by
    rw [sub_smul, one_smul]
  rw [hid, smul_smul]
  congr 1
  rw [poissonRate, ite_eq_left ht]
  rw [show -(2 * Real.pi * t * ‖ξ‖) = -(t * (2 * Real.pi * ‖ξ‖)) by ring]
  push_cast
  rfl

private theorem poissonQuadratic_inner_ae {t : ℝ} (ht : 0 < t) (f : L²) :
    (fun ξ ↦ (inner ℂ ((𝓕 f : L²) ξ)
      ((𝓕 (poissonQuotientL2 ht f) : L²) ξ)).re) =ᵐ[volume]
      fun ξ ↦ poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2 := by
  filter_upwards [fourier_poissonQuotientL2_ae ht f] with ξ hq
  rw [hq, inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact congrArg (poissonRate t (2 * Real.pi * ‖ξ‖) * ·)
    (inner_self_eq_norm_sq (𝕜 := ℂ) ((𝓕 f : L²) ξ))

/-- The positive spectral integrand is genuinely integrable at each positive height. -/
theorem integrable_poissonQuadratic_spectral {t : ℝ} (ht : 0 < t) (f : L²) :
    Integrable (fun ξ ↦ poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2) :=
  (Complex.reCLM.integrable_comp
    (L2.integrable_inner (𝓕 f) (𝓕 (poissonQuotientL2 ht f)))).congr
      (poissonQuadratic_inner_ae ht f)

/-- Plancherel evaluates the genuine spatial quadratic defect as its positive spectral integral. -/
theorem poissonQuadraticDefect_eq_integral {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonQuadraticDefect ht f =
      ∫ ξ, poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2 := by
  rw [poissonQuadraticDefect, ← (Lp.fourierTransformₗᵢ D E).inner_map_map]
  change (inner ℂ (𝓕 f) (𝓕 (poissonQuotientL2 ht f))).re = _
  rw [L2.inner_def]
  have h := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner (𝓕 f) (𝓕 (poissonQuotientL2 ht f)))
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  exact integral_congr_ae (poissonQuadratic_inner_ae ht f)

/-- Actual Poisson defects are nonnegative. -/
theorem poissonQuadraticDefect_nonneg {t : ℝ} (ht : 0 < t) (f : L²) :
    0 ≤ poissonQuadraticDefect ht f := by
  rw [poissonQuadraticDefect_eq_integral]
  apply integral_nonneg
  intro ξ
  exact mul_nonneg (poissonRate_bounds t (by positivity : 0 ≤ 2 * Real.pi * ‖ξ‖)).1
    (sq_nonneg _)

/-- The extended positive spectral defect, defined at every real height. -/
def poissonQuadraticSpectral (t : ℝ) (f : L²) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2)

theorem poissonQuadraticSpectral_eq_ofReal {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonQuadraticSpectral t f = ENNReal.ofReal (poissonQuadraticDefect ht f) := by
  rw [poissonQuadraticDefect_eq_integral]
  symm
  apply ofReal_integral_eq_lintegral_ofReal (integrable_poissonQuadratic_spectral ht f)
  filter_upwards with ξ
  exact mul_nonneg (poissonRate_bounds t (by positivity : 0 ≤ 2 * Real.pi * ‖ξ‖)).1
    (sq_nonneg _)

private theorem measurable_poissonQuadratic_integrand (t : ℝ) (f : L²) :
    Measurable (fun ξ ↦
      ENNReal.ofReal (poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2)) := by
  by_cases ht : 0 < t
  · simp only [poissonRate, ite_eq_left ht]
    exact (by fun_prop : Measurable (fun ξ : D ↦
      t⁻¹ * (1 - Real.exp (-(t * (2 * Real.pi * ‖ξ‖)))))).mul
        ((Lp.stronglyMeasurable (𝓕 f)).norm.measurable.pow_const 2) |>.ennreal_ofReal
  · simp only [poissonRate, ite_eq_right ht, zero_mul]
    exact measurable_const

private theorem poissonQuadratic_limit_integral (f : L²) :
    (∫⁻ ξ, ENNReal.ofReal (2 * Real.pi * ‖ξ‖ * ‖(𝓕 f : L²) ξ‖ ^ 2)) =
      ENNReal.ofReal (2 * Real.pi) * fourierEnergy 1 f := by
  rw [fourierEnergy]
  simp only [Real.rpow_one]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro ξ
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ← ofReal_norm]
  ring

/-- The true Poisson defects recover every actual isotropic half-order energy, even if infinite. -/
theorem tendsto_poissonQuadraticSpectral (f : L²) :
    Tendsto (fun t ↦ poissonQuadraticSpectral t f) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (2 * Real.pi) * fourierEnergy 1 f)) := by
  let F := fun t ξ ↦
    ENNReal.ofReal (poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2)
  let g := fun ξ ↦ ENNReal.ofReal (2 * Real.pi * ‖ξ‖ * ‖(𝓕 f : L²) ξ‖ ^ 2)
  have hlim ξ : Tendsto (fun t ↦ F t ξ) (𝓝[>] 0) (𝓝 (g ξ)) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp
      ((tendsto_poissonRate (2 * Real.pi * ‖ξ‖)).mul_const _)
  have hbound t : poissonQuadraticSpectral t f ≤ ∫⁻ ξ, g ξ := by
    apply lintegral_mono
    intro ξ
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (poissonRate_bounds t (by positivity : 0 ≤ 2 * Real.pi * ‖ξ‖)).2 (sq_nonneg _))
  have hlow : (∫⁻ ξ, g ξ) ≤
      liminf (fun t ↦ poissonQuadraticSpectral t f) (𝓝[>] 0) := by
    have hfatou := lintegral_liminf_le
      (μ := (volume : Measure D)) (u := 𝓝[>] (0 : ℝ))
      (fun t ↦ measurable_poissonQuadratic_integrand t f)
    change (∫⁻ ξ, liminf (fun t ↦ F t ξ) (𝓝[>] 0)) ≤
      liminf (fun t ↦ poissonQuadraticSpectral t f) (𝓝[>] 0) at hfatou
    have he : (fun ξ ↦ liminf (fun t ↦ F t ξ) (𝓝[>] 0)) = g :=
      funext fun ξ ↦ (hlim ξ).liminf_eq
    rwa [he] at hfatou
  rw [← poissonQuadratic_limit_integral]
  exact tendsto_of_le_liminf_of_limsup_le hlow
    (limsup_le_of_le (h := Eventually.of_forall hbound))

end PartialBalayage.Linear
