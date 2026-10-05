/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonFiniteWeakPDE
public import PartialBalayage.Linear.IsotropicGradientGraph
public import PartialBalayage.Linear.ExhaustionWeakEquation

/-!
# Genuine physical test closure and Poisson tests

The bounded physical generator pairing extends compact-test equations through the actual
defining Dirichlet closure. Genuine first-order Poisson states have physical Dirichlet
graphs, so these equations apply to the true height-one Poisson tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "H01ℝ" => H01 (univ : Set D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := ℂ) 2
local notation "WholeState" => IsotropicDirichletState (univ : Set D)

/-- A genuine bounded functional vanishing on all test graphs vanishes on actual `H01`. -/
theorem h01_functional_eq_zero_of_testGraphs (L : H01ℝ →L[ℝ] ℝ)
    (htest : ∀ (φ : D → ℝ) (hφ : IsTestFn univ φ), L hφ.toH01 = 0) :
    ∀ W : H01ℝ, L W = 0 := by
  let A := L ∘L (H01 (univ : Set D)).orthogonalProjectionOnto
  have hs : Submodule.span ℝ (testGraphSet (univ : Set D)) ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro Y ⟨φ, hφ, rfl⟩
    change L ((H01 univ).orthogonalProjectionOnto (hφ.toH01 : H1amb univ)) = 0
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact htest φ hφ
  intro (W : H01ℝ)
  have hw : (W : H1amb (univ : Set D)) ∈ closure
      ((Submodule.span ℝ (testGraphSet (univ : Set D))) : Set (H1amb (univ : Set D))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact W.property
  have hz := (closure_minimal hs A.isClosed_ker) hw
  change L ((H01 univ).orthogonalProjectionOnto (W : H1amb univ)) = 0 at hz
  simpa only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hz

/-- The actual bounded generator equation extends from compact smooth to all physical tests. -/
theorem poisson_generator_pairing_of_compact_tests (u q : L²ℝ)
    (htest : ∀ (φ : D → ℝ) (hφ : IsTestFn univ φ),
      ⟪u, h01PoissonRealGeneratorCLM hφ.toH01⟫ = ⟪q, h01RealValueCLM hφ.toH01⟫) :
    ∀ W : H01ℝ, ⟪u, h01PoissonRealGeneratorCLM W⟫ = ⟪q, h01RealValueCLM W⟫ := by
  let L := innerSL ℝ u ∘L h01PoissonRealGeneratorCLM - innerSL ℝ q ∘L h01RealValueCLM
  have hL : ∀ (φ : D → ℝ) (hφ : IsTestFn univ φ), L hφ.toH01 = 0 := by
    intro φ hφ
    exact sub_eq_zero.mpr (htest φ hφ)
  intro W
  exact sub_eq_zero.mp (h01_functional_eq_zero_of_testGraphs L hL W)

/-- The actual physical value of a compact test graph is its defining test function. -/
theorem h01RealValueCLM_test_ae (φ : D → ℝ) (hφ : IsTestFn univ φ) :
    h01RealValueCLM hφ.toH01 =ᵐ[volume] φ := by
  have he := zeroExtendL2_ae_restrict_value MeasurableSet.univ hφ.testCls
  have ht := hφ.mem_lp.coeFn_toLp
  simp only [Measure.restrict_univ] at he ht
  exact he.trans ht

/-- Actual compact tests are supported in the concrete expanding balls eventually. -/
theorem eventually_h01_test_supported_expanding_balls (φ : D → ℝ)
    (hφ : IsTestFn univ φ) :
    ∀ᶠ k : ℕ in atTop, ∀ᵐ x, x ∉ Metric.ball 0 (k + 1 : ℝ) →
      h01RealValueCLM hφ.toH01 x = 0 := by
  filter_upwards [eventually_compact_subset_expanding_balls hφ.2.1] with k hk
  filter_upwards [h01RealValueCLM_test_ae φ hφ] with x hx
  intro hxo
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport (fun hxs ↦ hxo (hk hxs))

/-- The genuine physical generator of an actually real first-order state is its true generator. -/
theorem h01PoissonGenerator_isotropicTwoH01 (V : H¹) (v : L²ℝ)
    (hV : isotropicEnergyValue 2 V = Complex.ofRealCLM.compLp v) :
    h01PoissonGenerator (isotropicTwoH01 V) = poissonGenerator V := by
  have hv : h01ComplexValueCLM (isotropicTwoH01 V) = isotropicEnergyValue 2 V :=
    complexGlobalGraphCoordinate_isotropicTwoH01 V v hV
  apply (Lp.fourierTransformₗᵢ D ℂ).injective
  change 𝓕 (h01PoissonGenerator (isotropicTwoH01 V)) = 𝓕 (poissonGenerator V)
  apply Lp.ext
  filter_upwards [fourier_h01PoissonGenerator_ae (isotropicTwoH01 V),
    fourier_poissonGenerator_ae V] with ξ hW hV
  rw [hW, hV, hv]

/-- Its actual physical real value is exactly the original real input class. -/
theorem h01RealValueCLM_isotropicTwoH01 (V : H¹) (v : L²ℝ)
    (hV : isotropicEnergyValue 2 V = Complex.ofRealCLM.compLp v) :
    h01RealValueCLM (isotropicTwoH01 V) = v := by
  have h := complexGlobalGraphCoordinate_isotropicTwoH01 V v hV
  change h01ComplexValueCLM (isotropicTwoH01 V) = isotropicEnergyValue 2 V at h
  rw [h01ComplexValueCLM_eq_complexify, hV] at h
  have hr := congrArg (fun f : L²ℂ ↦ Complex.reCLM.compLp f) h
  simpa only [re_compLp_complexify] using hr

/-- The actual half-order form against a real first-order test is its physical generator pairing. -/
theorem isotropicDirichletForm_halfTest_eq_h01_pairing (U : WholeState) (V : H¹)
    (v : L²ℝ) (hV : isotropicEnergyValue 2 V = Complex.ofRealCLM.compLp v) :
    isotropicDirichletForm univ U (isotropicWholeStateOfRealValue
      (isotropicHalfStateOfTwo V) v
        ((isotropicEnergyValue_isotropicHalfStateOfTwo V).trans hV)) =
      ⟪isotropicDirichletGlobalValue univ U,
        h01PoissonRealGeneratorCLM (isotropicTwoH01 V)⟫ := by
  rw [isotropicDirichletForm_apply, real_inner_complexLp]
  change 2 * Real.pi * (inner ℂ (isotropicEnergyData 1 U.val)
    (isotropicEnergyData 1 (isotropicHalfStateOfTwo V))).re = _
  have h := congrArg Complex.re (inner_isotropicHalfDataOfTwo U.val V)
  norm_num [Complex.mul_re, Complex.mul_im] at h
  rw [h, isotropicDirichlet_complexValue_eq MeasurableSet.univ]
  have hg := complexify_re_compLp_of_im_eq_zero (poissonGenerator V)
    (im_compLp_poissonGenerator_eq_zero V v hV)
  rw [← hg, re_inner_complexifyL2]
  change _ = ⟪_, Complex.reCLM.compLp (h01PoissonGenerator (isotropicTwoH01 V))⟫
  rw [h01PoissonGenerator_isotropicTwoH01 V v hV]

/-- Genuine physical `H01` equations give the actual Poisson-test half-order equation. -/
theorem poisson_test_equation_of_h01_generator_pairing (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ W : H01ℝ,
      ⟪isotropicDirichletGlobalValue univ U, h01PoissonRealGeneratorCLM W⟫ =
        ⟪q, h01RealValueCLM W⟫) {t : ℝ} (ht : 0 < t) (f : L²ℝ) :
    isotropicDirichletForm univ U (poissonRealHalfTest ht f) =
      ⟪q, poissonConvolutionL2 ht f⟫ := by
  let V := poissonSmoothedStateTwo ht (Complex.ofRealCLM.compLp f)
  have hv : isotropicEnergyValue 2 V =
      Complex.ofRealCLM.compLp (poissonConvolutionL2 ht f) := by
    rw [isotropicEnergyValue_poissonSmoothedStateTwo, poissonConvolutionL2_compLp ht]
  have h := isotropicDirichletForm_halfTest_eq_h01_pairing U V _ hv
  change isotropicDirichletForm univ U (poissonRealHalfTest ht f) = _ at h
  rw [h, hPDE, h01RealValueCLM_isotropicTwoH01 V _ hv]

end PartialBalayage.Linear
