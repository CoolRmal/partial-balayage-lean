/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonFiniteWeakPDE
public import PartialBalayage.Linear.PoissonH01TestClosure

/-!
# Genuine complex Poisson obstacle limits and their physical equations

A single complex norm cap is retained along the actual joint weak exhaustion. Testing
with both a physical real test and its imaginary multiple gives the full complex equation.
Actual Dirichlet test closure then extends it to every physical whole-space test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric FourierTransform
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal Topology

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := ℂ) 2
local notation "H01ℝ" => H01 (univ : Set D)

/-- The genuine isotropic generator respects complex scalar multiplication. -/
theorem poissonGenerator_smul (c : ℂ) (V : H¹) :
    poissonGenerator (c • V) = c • poissonGenerator V := by
  simp only [poissonGenerator, map_smul]
  rw [smul_comm (2 * Real.pi : ℂ) c, fourierInv_smul]

/-- Complexification and a complex multiple preserve actual eventual compact support. -/
theorem eventually_complex_h01_test_supported (φ : D → ℝ) (hφ : IsTestFn univ φ)
    (c : ℂ) :
    ∀ᶠ k : ℕ in atTop, ∀ᵐ x, x ∉ ball 0 (k + 1 : ℝ) →
      isotropicEnergyValue 2 (c • h01IsotropicStateTwo hφ.toH01) x = 0 := by
  filter_upwards [eventually_h01_test_supported_expanding_balls φ hφ] with k hk
  rw [map_smul, isotropicEnergyValue_h01IsotropicStateTwo, h01ComplexValueCLM_eq_complexify]
  filter_upwards [hk, Lp.coeFn_smul c
    (Complex.ofRealCLM.compLp (h01RealValueCLM hφ.toH01)),
    Complex.ofRealCLM.coeFn_compLp (h01RealValueCLM hφ.toH01)] with x hx hs hc
  intro hxo
  rw [hs, Pi.smul_apply, hc, hx hxo, map_zero, smul_zero]

/-- The actual bounded physical functional extends through the true compact test closure. -/
theorem complex_generator_pairing_of_compact_tests (u q : L²)
    (htest : ∀ (φ : D → ℝ) (hφ : IsTestFn univ φ),
      inner ℂ u (h01PoissonGenerator hφ.toH01) = inner ℂ q (h01ComplexValueCLM hφ.toH01)) :
    ∀ W : H01ℝ, inner ℂ u (h01PoissonGenerator W) = inner ℂ q (h01ComplexValueCLM W) := by
  let L : H01ℝ →L[ℝ] ℂ :=
    (innerSL ℂ u).restrictScalars ℝ ∘L h01PoissonGeneratorCLM -
      (innerSL ℂ q).restrictScalars ℝ ∘L h01ComplexValueCLM
  have hz (φ : D → ℝ) (hφ : IsTestFn univ φ) : L hφ.toH01 = 0 :=
    sub_eq_zero.mpr (htest φ hφ)
  have hr := h01_functional_eq_zero_of_testGraphs (Complex.reCLM ∘L L)
    (fun φ hφ ↦ by change (L hφ.toH01).re = 0; rw [hz φ hφ, Complex.zero_re])
  have hi := h01_functional_eq_zero_of_testGraphs (Complex.imCLM ∘L L)
    (fun φ hφ ↦ by change (L hφ.toH01).im = 0; rw [hz φ hφ, Complex.zero_im])
  intro W
  apply sub_eq_zero.mp
  change L W = 0
  exact Complex.ext (hr W) (hi W)

/-- The constructed complex obstacle limit has the genuine full complex physical PDE,
finite half-order energy, and the exact limiting norm-mass inequality. -/
theorem exists_wholeSpace_complex_poisson_weak_PDE (hn : 0 < n) (f : L²)
    (hf : Integrable (f : D → ℂ)) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ ν u : L²,
      ν ∈ normMassCap volume κ
        ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩ ∧
      Integrable (u : D → ℂ) ∧ fourierEnergy 1 u ≠ ⊤ ∧
      2 * Real.pi * (fourierEnergy 1 u).toReal + (κ : ℝ) * ∫ x, ‖u x‖ ≤ ⟪f, u⟫ ∧
      ∀ W : H01ℝ, inner ℂ u (h01PoissonGenerator W) =
        inner ℂ (f - ν) (h01ComplexValueCLM W) := by
  let Ω : ℕ → Set D := fun k ↦ ball 0 (k + 1 : ℝ)
  have hΩ : ∀ k, MeasurableSet (Ω k) := fun _ ↦ measurableSet_ball
  have hfin : ∀ k, volume (Ω k) ≠ ⊤ := fun _ ↦
    (isBounded_ball.measure_lt_top (μ := volume)).ne
  let mass : ℝ≥0 := ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩
  obtain ⟨t, ht, ν, u, νlimit, limit, l, hheight, heq, _, hν,
    hlne, hl, hνt, hut, ⟨B, hB⟩, hi, hE, henergy⟩ :=
    exists_poissonFinite_joint_weak_limit hn Ω hΩ hfin f hf κ mass hκ le_rfl
  let : l.NeBot := hlne
  refine ⟨νlimit, limit, hν, hi, hE, henergy, ?_⟩
  apply complex_generator_pairing_of_compact_tests
  intro φ hφ
  have h (c : ℂ) := poisson_generator_pairing_of_joint_limit Ω hΩ t ht ν u f
    νlimit limit hl hheight hνt hut B hB heq (c • h01IsotropicStateTwo hφ.toH01)
      (eventually_complex_h01_test_supported φ hφ c)
  simp only [poissonGenerator_smul, map_smul,
    isotropicEnergyValue_h01IsotropicStateTwo] at h
  have hr := h 1
  simp only [one_smul, real_inner_complexLp] at hr
  have him := h Complex.I
  simp only [real_inner_complexLp, inner_smul_right, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at him
  exact Complex.ext hr (neg_injective him)

end PartialBalayage.Linear.ComplexPoisson
