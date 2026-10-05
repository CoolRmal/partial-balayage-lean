/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonH01TestClosure
public import PartialBalayage.Linear.IsotropicPoissonTestEquation
public import PartialBalayage.Linear.WeakDirichletComplementarity
public import PartialBalayage.Linear.WholeSpaceDensityMass

/-!
# Actual signed isotropic Poisson partial balayage

The genuine finite signed Poisson obstacles on expanding balls yield an actual whole-space
half-order state and capped density. Their true energy-mass balances pass along the same
joint weak selection. Actual compact tests extend through physical Dirichlet closure to
Poisson tests, which recover the full half-order weak equation and cap complementarity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "WholeState" => IsotropicDirichletState (univ : Set D)

/-- The actual ball exhaustion gives a genuine capped density, true half-energy state,
and actual Poisson-test equations with the same limiting energy-mass inequality. -/
theorem exists_wholeSpace_signed_poisson_weak_PDE (hn : 0 < n) (f : L²ℝ)
    (hf : Integrable (f : D → ℝ)) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : L²ℝ) (U : WholeState),
      ν ∈ normMassCap volume κ
        ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩ ∧
      Integrable (isotropicDirichletGlobalValue univ U : D → ℝ) ∧
      isotropicDirichletForm univ U U + (κ : ℝ) *
        ∫ x, ‖isotropicDirichletGlobalValue univ U x‖ ≤
          ⟪f, isotropicDirichletGlobalValue univ U⟫ ∧
      ∀ g : L²ℝ, isotropicDirichletForm univ U
        (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) g) =
          ⟪f - ν, poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) g⟫ := by
  let Ω : ℕ → Set D := fun k ↦ ball 0 (k + 1 : ℝ)
  have hΩ : ∀ k, MeasurableSet (Ω k) := fun _ ↦ measurableSet_ball
  have hfin : ∀ k, volume (Ω k) ≠ ⊤ := fun _ ↦
    (isBounded_ball.measure_lt_top (μ := volume)).ne
  let mass : ℝ≥0 := ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩
  obtain ⟨t, ht, ν, u, νlimit, limit, l, hheight, heq, _, hν,
    hlne, hl, hνt, hut, ⟨B, hB⟩, hi, hE, henergy⟩ :=
    exists_poissonFinite_joint_weak_limit hn Ω hΩ hfin f hf κ mass hκ le_rfl
  let : l.NeBot := hlne
  let U := isotropicRealStateOfFiniteEnergy limit hE
  have hv : isotropicDirichletGlobalValue univ U = limit :=
    isotropicDirichletGlobalValue_isotropicRealStateOfFiniteEnergy limit hE
  have hPDE : ∀ W : H01 (univ : Set D),
      ⟪limit, h01PoissonRealGeneratorCLM W⟫ = ⟪f - νlimit, h01RealValueCLM W⟫ := by
    apply poisson_generator_pairing_of_compact_tests
    intro φ hφ
    exact poisson_generator_pairing_of_joint_limit Ω hΩ t ht ν u f νlimit limit hl
      hheight hνt hut B hB heq hφ.toH01
      (eventually_h01_test_supported_expanding_balls φ hφ)
  refine ⟨νlimit, U, hν, hv.symm ▸ hi, ?_, ?_⟩
  · rw [hv, isotropicDirichletForm_isotropicRealStateOfFiniteEnergy]
    exact henergy
  · intro g
    apply poisson_test_equation_of_h01_generator_pairing U (f - νlimit)
      (fun W ↦ hv.symm ▸ hPDE W)

/-- The true Poisson equations and limiting balance force actual alignment and saturation. -/
theorem signed_poisson_alignment_saturation (U : WholeState) (f ν : L²ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hν : ν ∈ normCap volume κ)
    (hi : Integrable (isotropicDirichletGlobalValue univ U : D → ℝ))
    (henergy : isotropicDirichletForm univ U U +
      κ * ∫ x, ‖isotropicDirichletGlobalValue univ U x‖ ≤
        ⟪f, isotropicDirichletGlobalValue univ U⟫)
    (hTest : ∀ g : L²ℝ, isotropicDirichletForm univ U
      (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) g) =
        ⟪f - ν, poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) g⟫) :
    (∀ᵐ x, isotropicDirichletGlobalValue univ U x ≠ 0 →
      ν x = (κ / ‖isotropicDirichletGlobalValue univ U x‖) •
        isotropicDirichletGlobalValue univ U x) ∧
    (∀ᵐ x, isotropicDirichletGlobalValue univ U x ≠ 0 → ‖ν x‖ = κ) := by
  have he := isotropicDirichletForm_self_of_Poisson_test_equations U (f - ν) hTest
  rw [inner_sub_left] at he
  apply ae_alignment_saturation_of_pairing_ge hκ ν
    (isotropicDirichletGlobalValue univ U) hν hi
  linarith

/-- Every actual integrable real `L²` input has genuine signed isotropic partial balayage,
with actual Poisson equations, full mass cap, and cap complementarity. -/
theorem exists_wholeSpace_signed_poisson_balayage (hn : 0 < n) (f : L²ℝ)
    (hf : Integrable (f : D → ℝ)) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : L²ℝ) (U : WholeState),
      ν ∈ normMassCap volume κ
        ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩ ∧
      Integrable (isotropicDirichletGlobalValue univ U : D → ℝ) ∧
      (∀ g : L²ℝ, isotropicDirichletForm univ U
        (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) g) =
          ⟪f - ν, poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) g⟫) ∧
      (∀ᵐ x, isotropicDirichletGlobalValue univ U x ≠ 0 →
        ν x = ((κ : ℝ) / ‖isotropicDirichletGlobalValue univ U x‖) •
          isotropicDirichletGlobalValue univ U x) ∧
      (∀ᵐ x, isotropicDirichletGlobalValue univ U x ≠ 0 → ‖ν x‖ = (κ : ℝ)) := by
  obtain ⟨ν, U, hν, hi, he, htest⟩ :=
    exists_wholeSpace_signed_poisson_weak_PDE hn f hf κ hκ
  have ha := signed_poisson_alignment_saturation U f ν κ.coe_nonneg hν.1 hi he htest
  exact ⟨ν, U, hν, hi, htest, ha⟩

end PartialBalayage.Linear
