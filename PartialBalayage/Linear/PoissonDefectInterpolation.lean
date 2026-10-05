/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonQuadraticSpectral
public import PartialBalayage.Linear.FourierCoercivity

/-!
# Genuine low and high frequency estimates for Poisson defects

The actual bounded positive-height defect controls all frequencies outside a
fixed ball at sufficiently small positive heights. No half-order graph membership
is assumed on the ordinary L2 inputs.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Metric Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)

/-- Every genuine positive-height Poisson rate increases with the actual frequency. -/
theorem poissonRate_mono_frequency {t : ℝ} (ht : 0 < t) {r s : ℝ} (hrs : r ≤ s) :
    poissonRate t r ≤ poissonRate t s := by
  rw [poissonRate, poissonRate, ite_eq_left ht, ite_eq_left ht]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
  have h := Real.exp_le_exp.mpr (show -(t * s) ≤ -(t * r) by nlinarith)
  linarith

/-- At sufficiently small positive heights the actual rate at radius R is bounded below. -/
theorem eventually_poissonRate_lower {R : ℝ} (hR : 0 < R) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.pi * R ≤ poissonRate t (2 * Real.pi * R) := by
  have h : Real.pi * R < 2 * Real.pi * R := by nlinarith [Real.pi_pos]
  exact (tendsto_poissonRate (2 * Real.pi * R)).eventually
    (eventually_ge_nhds h)

/-- The actual defect controls the full high-frequency squared mass. -/
theorem setLIntegral_fourier_high_le_poissonDefect {t R : ℝ} (ht : 0 < t)
    (hR : 0 < R) (hrate : Real.pi * R ≤ poissonRate t (2 * Real.pi * R)) (f : L²) :
    (∫⁻ ξ in (closedBall (0 : D) R)ᶜ, ‖(𝓕 f : L²) ξ‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal ((Real.pi * R)⁻¹) * poissonQuadraticSpectral t f := by
  have hp : 0 < Real.pi * R := mul_pos Real.pi_pos hR
  have hw (ξ : D) (hξ : ξ ∈ (closedBall (0 : D) R)ᶜ) :
      1 ≤ (Real.pi * R)⁻¹ * poissonRate t (2 * Real.pi * ‖ξ‖) := by
    have hξR : R ≤ ‖ξ‖ := le_of_lt (by
      simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hξ)
    have hle := hrate.trans (poissonRate_mono_frequency ht
      (mul_le_mul_of_nonneg_left hξR (by positivity : 0 ≤ 2 * Real.pi)))
    exact (le_inv_mul_iff₀ hp).mpr (by simpa only [mul_one] using hle)
  calc
    _ ≤ ∫⁻ ξ in (closedBall (0 : D) R)ᶜ, ENNReal.ofReal ((Real.pi * R)⁻¹) *
        ENNReal.ofReal (poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2) := by
      apply setLIntegral_mono' measurableSet_closedBall.compl
      intro ξ hξ
      rw [ENNReal.ofReal_mul (poissonRate_bounds t (by positivity)).1,
        ENNReal.ofReal_pow (norm_nonneg _), ← ofReal_norm]
      have h : 1 ≤ ENNReal.ofReal ((Real.pi * R)⁻¹) *
          ENNReal.ofReal (poissonRate t (2 * Real.pi * ‖ξ‖)) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
        exact_mod_cast ENNReal.ofReal_le_ofReal (hw ξ hξ)
      simpa only [mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc, ← ofReal_norm] using
        mul_le_mul_right h (‖(𝓕 f : L²) ξ‖ₑ ^ (2 : ℕ))
    _ ≤ ∫⁻ ξ, ENNReal.ofReal ((Real.pi * R)⁻¹) *
        ENNReal.ofReal (poissonRate t (2 * Real.pi * ‖ξ‖) * ‖(𝓕 f : L²) ξ‖ ^ 2) :=
      setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The true low/high splitting estimate uses only the actual bounded Poisson defect. -/
theorem enorm_sq_le_poisson_defect_split {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (hrate : Real.pi * R ≤ poissonRate t (2 * Real.pi * R)) (f : L²)
    (hf : Integrable (f : D → E)) :
    ‖f‖ₑ ^ (2 : ℕ) ≤
      ENNReal.ofReal ((∫ x, ‖f x‖) ^ 2) * volume (closedBall (0 : D) R) +
        ENNReal.ofReal ((Real.pi * R)⁻¹) *
          ENNReal.ofReal (poissonQuadraticDefect ht f) := by
  rw [enorm_sq_eq_lintegral_fourier,
    ← lintegral_add_compl _ measurableSet_closedBall]
  have hh := setLIntegral_fourier_high_le_poissonDefect ht hR hrate f
  rw [poissonQuadraticSpectral_eq_ofReal ht] at hh
  exact add_le_add (setLIntegral_fourier_enorm_sq_le f hf _) hh

/-- The actual real low/high estimate has a finite positive-height energy term. -/
theorem norm_sq_le_poisson_defect_split {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (hrate : Real.pi * R ≤ poissonRate t (2 * Real.pi * R)) (f : L²)
    (hf : Integrable (f : D → E)) :
    ‖f‖ ^ 2 ≤ (∫ x, ‖f x‖) ^ 2 * (volume (closedBall (0 : D) R)).toReal +
      (Real.pi * R)⁻¹ * poissonQuadraticDefect ht f := by
  have hv : volume (closedBall (0 : D) R) ≠ ⊤ :=
    (isCompact_closedBall (0 : D) R).measure_lt_top.ne
  have hM : 0 ≤ (∫ x, ‖f x‖) ^ 2 := sq_nonneg _
  have hD : 0 ≤ (Real.pi * R)⁻¹ := by positivity
  have hE := poissonQuadraticDefect_nonneg ht f
  have hfin : ENNReal.ofReal ((∫ x, ‖f x‖) ^ 2) * volume (closedBall (0 : D) R) +
      ENNReal.ofReal ((Real.pi * R)⁻¹) *
        ENNReal.ofReal (poissonQuadraticDefect ht f) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have he := ENNReal.toReal_mono hfin
    (enorm_sq_le_poisson_defect_split ht hR hrate f hf)
  simpa only [← ofReal_norm, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ENNReal.toReal_ofReal hD, ENNReal.toReal_ofReal hE] using he

/-- The actual ordinary-input interpolation has the mass-plus-square-root-defect form. -/
theorem norm_le_poisson_defect_split {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (hrate : Real.pi * R ≤ poissonRate t (2 * Real.pi * R)) (f : L²)
    (hf : Integrable (f : D → E)) :
    ‖f‖ ≤ Real.sqrt (volume (closedBall (0 : D) R)).toReal * (∫ x, ‖f x‖) +
      Real.sqrt ((Real.pi * R)⁻¹) * Real.sqrt (poissonQuadraticDefect ht f) := by
  have hM : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hD : 0 ≤ (Real.pi * R)⁻¹ := by positivity
  have hE := poissonQuadraticDefect_nonneg ht f
  have hs := norm_sq_le_poisson_defect_split ht hR hrate f hf
  have hv := Real.sq_sqrt (volume (closedBall (0 : D) R)).toReal_nonneg
  have hd := Real.sq_sqrt hD
  have he := Real.sq_sqrt hE
  have hp := mul_nonneg (Real.sqrt_nonneg (volume (closedBall (0 : D) R)).toReal) hM
  have hq := mul_nonneg (Real.sqrt_nonneg ((Real.pi * R)⁻¹))
    (Real.sqrt_nonneg (poissonQuadraticDefect ht f))
  nlinarith [mul_nonneg hp hq, norm_nonneg f]

end PartialBalayage.Linear
