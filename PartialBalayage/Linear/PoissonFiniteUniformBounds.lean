/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonDefectInterpolation
public import PartialBalayage.Linear.PoissonDirichletEnergyMass

/-!
# Actual uniform bounds from regularized Poisson obstacle balances

The genuine defect interpolation and fixed-input balance bound the full L2 state,
its whole-space L1 mass and its positive-height energy independently of the domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Metric Set
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)

/-- Actual complexification preserves the true L2 norm of a real input. -/
theorem norm_complexifyL2 (f : L²ℝ) : ‖Complex.ofRealCLM.compLp f‖ = ‖f‖ := by
  have h := re_inner_complexifyL2 f f
  have hc := inner_self_eq_norm_sq (𝕜 := ℂ) (Complex.ofRealCLM.compLp f)
  rw [RCLike.re_eq_complex_re] at hc
  rw [hc, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg f, norm_nonneg (Complex.ofRealCLM.compLp f)]

/-- Complexifying an actual integrable real L2 representative preserves integrability. -/
theorem integrable_complexifyL2 (f : L²ℝ) (hf : Integrable (f : D → ℝ)) :
    Integrable (Complex.ofRealCLM.compLp f : D → ℂ) :=
  (Complex.ofRealCLM.integrable_comp hf).congr (Complex.ofRealCLM.coeFn_compLp' f).symm

/-- Actual complexification preserves the physical whole-space norm mass. -/
theorem integral_norm_complexifyL2 (f : L²ℝ) :
    (∫ x, ‖Complex.ofRealCLM.compLp f x‖) = ∫ x, ‖f x‖ := by
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
  simp only [hx, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs]

/-- A fixed input and cap give actual domain-independent state, mass and defect bounds. -/
theorem exists_poisson_balance_uniform_bounds (hn : 0 < n) (f : L²ℝ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ {t : ℝ} (ht : 0 < t),
      Real.pi * R ≤ poissonRate t (2 * Real.pi * R) →
      ∀ u : L²ℝ, Integrable (u : D → ℝ) →
        poissonQuadraticDefect ht (Complex.ofRealCLM.compLp u) +
          κ * (∫ x, ‖u x‖) ≤ inner ℝ f u →
        poissonQuadraticDefect ht (Complex.ofRealCLM.compLp u) ≤ C ∧
          (∫ x, ‖u x‖) ≤ C ∧ ‖u‖ ^ 2 ≤ C := by
  have hdim : 0 < Module.finrank ℝ D := by simpa using hn
  obtain ⟨R, hR, hsmall⟩ := exists_small_fourier_radius (X := D) hdim hκ (norm_nonneg f)
  let A := Real.sqrt (volume (closedBall (0 : D) R)).toReal
  let D₀ := (Real.pi * R)⁻¹
  let E₀ := 4 * ‖f‖ ^ 2 * D₀
  let M₀ := 2 * ‖f‖ ^ 2 * D₀ / κ
  let N₀ := A * M₀ + 2 * ‖f‖ * D₀
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hD : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  have hN₀ : 0 ≤ N₀ := add_nonneg (mul_nonneg hA hM₀) (by positivity)
  refine ⟨R, 1 + E₀ + M₀ + N₀ ^ 2, hR, by positivity, ?_⟩
  intro t ht hrate u hu hbalance
  let e := poissonQuadraticDefect ht (Complex.ofRealCLM.compLp u)
  let m := ∫ x, ‖u x‖
  have he : 0 ≤ e := poissonQuadraticDefect_nonneg ht _
  have hm : 0 ≤ m := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hi := norm_le_poisson_defect_split ht hR hrate (Complex.ofRealCLM.compLp u)
    (integrable_complexifyL2 u hu)
  rw [norm_complexifyL2, integral_norm_complexifyL2] at hi
  change ‖u‖ ≤ A * m + Real.sqrt D₀ * Real.sqrt e at hi
  change e + κ * m ≤ inner ℝ f u at hbalance
  have hsub : e / 2 + κ * m ≤ ‖f‖ * ‖u‖ := by
    have hinner := real_inner_le_norm f u
    linarith
  have hb := obstacle_sublevel_bounds_of_interpolation hm hD he hκ
    (norm_nonneg f) hsmall hi hsub
  have hE : e ≤ E₀ := hb.1
  have hM : m ≤ M₀ := hb.2
  have hs : Real.sqrt e ≤ 2 * ‖f‖ * Real.sqrt D₀ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    dsimp [E₀] at hE
    nlinarith [Real.sq_sqrt hD]
  have hN : ‖u‖ ≤ N₀ := by
    have hh : Real.sqrt D₀ * Real.sqrt e ≤ 2 * ‖f‖ * D₀ := by
      calc
        _ ≤ Real.sqrt D₀ * (2 * ‖f‖ * Real.sqrt D₀) :=
          mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg D₀)
        _ = 2 * ‖f‖ * D₀ := by
          rw [show Real.sqrt D₀ * (2 * ‖f‖ * Real.sqrt D₀) =
            2 * ‖f‖ * (Real.sqrt D₀) ^ 2 by ring, Real.sq_sqrt hD]
    exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hM hA) hh)
  have hNsq := pow_le_pow_left₀ (norm_nonneg u) hN 2
  exact ⟨by change e ≤ _; nlinarith [sq_nonneg N₀],
    by change m ≤ _; nlinarith [sq_nonneg N₀], by nlinarith⟩

end PartialBalayage.Linear
