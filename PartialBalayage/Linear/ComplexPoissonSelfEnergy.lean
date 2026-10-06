/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonRegularity

/-!
# Actual complex Poisson states and the physical self-energy identity

The genuine complex weak equation constructs the full first-order Fourier graph.
Its half-order state gives the actual self-energy pairing without an extra certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := ℂ) 2

/-- The actual scalar complex L² pairing has the usual real-part real pairing. -/
theorem complexLp_re_inner (u q : L²ℂ) : (inner ℂ u q).re = inner ℝ u q := by
  rw [L2.inner_def, L2.inner_def]
  change Complex.reCLM (∫ x, inner ℂ (u x) (q x)) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) u q)]
  apply integral_congr_ae
  filter_upwards with x
  rfl

/-- The actual complex physical equation supplies its genuine first-order energy state. -/
theorem exists_complex_poisson_state_of_h01_equation (u q : L²ℂ)
    (hPDE : ∀ W : H01 (univ : Set D),
      inner ℂ u (h01PoissonGenerator W) = inner ℂ q (h01ComplexValueCLM W)) :
    ∃ V : H¹, isotropicEnergyValue 2 V = u ∧ poissonGenerator V = q := by
  let d : L²ℂ := (2 * Real.pi : ℂ)⁻¹ • 𝓕 q
  let p : PiLp 2 (fun _ : Fin 2 ↦ L²ℂ) :=
    WithLp.toLp 2 (Fin.cons u (fun _ : Fin 1 ↦ d))
  have hp : p ∈ isotropicEnergyGraph (X := D) (E := ℂ) 2 := by
    change ∀ᵐ ξ, d ξ = ((‖ξ‖ ^ ((2 : ℝ) / 2) : ℝ) : ℂ) • (𝓕 u : L²ℂ) ξ
    norm_num only [div_self, Real.rpow_one]
    filter_upwards [complex_isotropicNormFourier_ae_of_h01_equation u q hPDE,
      Lp.coeFn_smul (2 * Real.pi : ℂ)⁻¹ (𝓕 q)] with ξ hξ hd
    exact hd.trans hξ.symm
  let V : H¹ := ⟨p, hp⟩
  refine ⟨V, rfl, ?_⟩
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
  change 𝓕⁻ ((2 * Real.pi : ℂ) • ((2 * Real.pi : ℂ)⁻¹ • 𝓕 q)) = q
  rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, fourierInv_fourier_eq]

/-- Genuine half-order energy equals the real pairing with the actual complex source. -/
theorem complex_poisson_self_energy_of_h01_equation (u q : L²ℂ)
    (hPDE : ∀ W : H01 (univ : Set D),
      inner ℂ u (h01PoissonGenerator W) = inner ℂ q (h01ComplexValueCLM W)) :
    2 * Real.pi * (fourierEnergy 1 u).toReal = inner ℝ q u := by
  obtain ⟨V, hv, hg⟩ := exists_complex_poisson_state_of_h01_equation u q hPDE
  have h := inner_isotropicHalfDataOfTwo (isotropicHalfStateOfTwo V) V
  have he : (fourierEnergy 1 u).toReal =
      ‖isotropicEnergyData 1 (isotropicHalfStateOfTwo V)‖ ^ 2 := by
    rw [← hv, ← isotropicEnergyValue_isotropicHalfStateOfTwo,
      ← isotropicEnergyData_enorm_sq, ← ofReal_norm, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  have hr := congrArg Complex.re h
  have hπre : (2 * Real.pi : ℂ).re = 2 * Real.pi := by simp
  have hπim : (2 * Real.pi : ℂ).im = 0 := by simp
  have hself := inner_self_eq_norm_sq (𝕜 := ℂ)
    (isotropicEnergyData 1 (isotropicHalfStateOfTwo V))
  rw [RCLike.re_eq_complex_re] at hself
  rw [Complex.mul_re, hπre, hπim, zero_mul, sub_zero, hself,
    isotropicEnergyValue_isotropicHalfStateOfTwo, hv, hg] at hr
  rw [he]
  exact hr.trans ((complexLp_re_inner u q).trans (real_inner_comm u q).symm)

end PartialBalayage.Linear
