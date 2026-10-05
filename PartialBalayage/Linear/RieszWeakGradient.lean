/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.IsotropicGradientGraph
public import PartialBalayage.Linear.IsotropicWeakPDERegularity
public import PartialBalayage.Linear.ProjectionHessianIdentity
public import PartialBalayage.Linear.SobolevZeroSet

/-!
# The full actual Riesz vector is the genuine weak gradient

The actual whole-space half-order weak equation gives genuine first-order regularity.
Its full frequency-norm identity identifies every actual Riesz coordinate with the
physical weak gradient. Zero-set locality then applies to the complete vector.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²V" => Lp V 2 (volume : Measure D)
local notation "WholeState" => IsotropicDirichletState (univ : Set D)

/-- Each actual full-vector Riesz coordinate has its genuine scalar Fourier symbol. -/
theorem fourier_rieszCoordinate_ae (f : L²ℂ) (i : Fin n) :
    (𝓕 ((projectionCoordinateCLM i).compLp (rieszL2 f)) : L²ℂ) =ᵐ[volume]
      fun ξ ↦ (𝓕 f : L²ℂ) ξ * (Complex.I * (ξ i : ℂ) / (‖ξ‖ : ℂ)) := by
  rw [fourier_compLp]
  have hF : (𝓕 (rieszL2 f) : L²V) =
      multiplyVectorL2 rieszSymbol measurable_rieszSymbol norm_rieszSymbol_le (𝓕 f) := by
    change 𝓕 (𝓕⁻ (multiplyVectorL2 rieszSymbol measurable_rieszSymbol
      norm_rieszSymbol_le (𝓕 f))) = _
    exact fourier_fourierInv_eq _
  rw [hF]
  filter_upwards [(projectionCoordinateCLM i).coeFn_compLp
    (multiplyVectorL2 rieszSymbol measurable_rieszSymbol norm_rieszSymbol_le (𝓕 f)),
    (vectorSymbol_memLp rieszSymbol measurable_rieszSymbol norm_rieszSymbol_le
      (𝓕 f)).coeFn_toLp] with ξ hc hm
  change (multiplyVectorL2 rieszSymbol measurable_rieszSymbol norm_rieszSymbol_le
    (𝓕 f) : L²V) ξ = (𝓕 f : L²ℂ) ξ • rieszSymbol ξ at hm
  rw [hc, hm]
  change ((𝓕 f : L²ℂ) ξ • rieszSymbol ξ) i = _
  simp only [PiLp.smul_apply, smul_eq_mul, rieszSymbol_apply]

/-- The actual physical gradient supplied by the genuine half-order weak equation. -/
def rieszWeakPDEH01 (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ W : WholeState, isotropicDirichletForm univ U W =
      inner ℝ q (isotropicDirichletGlobalValue univ W)) : H01 (univ : Set D) :=
  isotropicTwoH01 (isotropicWeakPDEStateTwo U q hPDE)

/-- Its actual complex value is exactly the original half-order state value. -/
theorem complexGlobalGraphCoordinate_rieszWeakPDEH01 (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ W : WholeState, isotropicDirichletForm univ U W =
      inner ℝ q (isotropicDirichletGlobalValue univ W)) :
    complexGlobalGraphCoordinateCLM 0 (rieszWeakPDEH01 U q hPDE : H1amb univ) =
      isotropicEnergyValue 1 U.val := by
  exact (complexGlobalGraphCoordinate_isotropicTwoH01 _
    (isotropicDirichletGlobalValue univ U)
    (isotropicDirichlet_complexValue_eq MeasurableSet.univ U)).trans rfl

/-- The actual full-norm Fourier identity identifies every genuine Riesz coordinate. -/
theorem rieszCoordinate_eq_gradient_of_norm_fourier (G : H01 (univ : Set D))
    (f : L²ℂ) (q : L²ℝ)
    (hValue : complexGlobalGraphCoordinateCLM 0 (G : H1amb univ) = f)
    (hFrequency : ∀ᵐ ξ, (‖ξ‖ : ℂ) • (𝓕 f : L²ℂ) ξ =
      (2 * Real.pi : ℂ)⁻¹ • (𝓕 (Complex.ofRealCLM.compLp q) : L²ℂ) ξ) (i : Fin n) :
    (projectionCoordinateCLM i).compLp (rieszL2 (Complex.ofRealCLM.compLp q)) =
      complexGlobalGraphCoordinateCLM i.succ (G : H1amb univ) := by
  apply (Lp.fourierTransformₗᵢ D ℂ).injective
  change (𝓕 ((projectionCoordinateCLM i).compLp
    (rieszL2 (Complex.ofRealCLM.compLp q))) : L²ℂ) =
      𝓕 (complexGlobalGraphCoordinateCLM i.succ (G : H1amb univ))
  apply Lp.ext
  filter_upwards [fourier_rieszCoordinate_ae (Complex.ofRealCLM.compLp q) i,
    fourier_complexGlobalGraphCoordinate_partial_ae (G) i,
    hFrequency] with ξ hr hg hn
  rw [hValue] at hg
  rw [hr, hg]
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, smul_eq_mul]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hnorm : (‖ξ‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
    have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
    have hq : (𝓕 (Complex.ofRealCLM.compLp q) : L²ℂ) ξ =
        (2 * Real.pi : ℂ) * ((‖ξ‖ : ℂ) *
          (𝓕 (f) : L²ℂ) ξ) := by
      have h := congrArg (fun z : ℂ ↦ (2 * Real.pi : ℂ) * z) hn
      simp only [smul_eq_mul, mul_inv_cancel_left₀ hπ] at h
      exact h.symm
    rw [hq]
    field_simp [hnorm]

/-- Every genuine Riesz output coordinate is the actual physical weak-gradient class. -/
theorem rieszCoordinate_eq_weakGradient (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ W : WholeState, isotropicDirichletForm univ U W =
      inner ℝ q (isotropicDirichletGlobalValue univ W)) (i : Fin n) :
    (projectionCoordinateCLM i).compLp (rieszL2 (Complex.ofRealCLM.compLp q)) =
      complexGlobalGraphCoordinateCLM i.succ (rieszWeakPDEH01 U q hPDE : H1amb univ) := by
  exact rieszCoordinate_eq_gradient_of_norm_fourier _ _ q
    (complexGlobalGraphCoordinate_rieszWeakPDEH01 U q hPDE)
    (isotropicWeakPDE_norm_fourier_ae U q hPDE) i

/-- The full actual Riesz vector vanishes almost everywhere on the true state value's zero set. -/
theorem ae_rieszL2_eq_zero_on_isotropicValue_zero (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ W : WholeState, isotropicDirichletForm univ U W =
      inner ℝ q (isotropicDirichletGlobalValue univ W)) :
    ∀ᵐ x, isotropicDirichletGlobalValue univ U x = 0 →
      rieszL2 (Complex.ofRealCLM.compLp q) x = 0 := by
  let G := rieszWeakPDEH01 U q hPDE
  have hv : ((G : H1amb univ) 0 : D → ℝ) =ᵐ[volume]
      isotropicDirichletGlobalValue univ U :=
    (isotropicTwoH01_value_ae (isotropicWeakPDEStateTwo U q hPDE)).trans
      (isotropicDirichletGlobalValue_ae U).symm
  have hz : ∀ᵐ x, ((G : H1amb univ) 0 x : ℝ) = 0 →
      ∀ i : Fin n, ((G : H1amb univ) i.succ x : ℝ) = 0 := by
    simpa only [Measure.restrict_univ] using
      ae_all_gradients_eq_zero_on_value_zero isOpen_univ G
  have hc : ∀ᵐ x, ∀ i : Fin n, rieszL2 (Complex.ofRealCLM.compLp q) x i =
      (((G : H1amb univ) i.succ x : ℝ) : ℂ) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [projectionCoordinateCLM_ae (rieszL2 (Complex.ofRealCLM.compLp q)) i,
      Lp.ext_iff.mp (rieszCoordinate_eq_weakGradient U q hPDE i),
      complexGlobalGraphCoordinateCLM_ae i.succ (G : H1amb univ)] with x hr he hg
    exact hr.symm.trans (he.trans hg)
  filter_upwards [hv, hz, hc] with x hv hz hc
  intro hx
  ext i
  change rieszL2 (Complex.ofRealCLM.compLp q) x i = 0
  rw [hc i, hz (hv.trans hx) i, Complex.ofReal_zero]

/-- Actual Poisson-test equations already give the full Riesz-vector zero-set cancellation. -/
theorem ae_rieszL2_eq_zero_of_Poisson_test_equations (U : WholeState) (q : L²ℝ)
    (hTest : ∀ f : L²ℝ, isotropicDirichletForm univ U
      (poissonRealHalfTest (by norm_num : (0 : ℝ) < 1) f) =
        inner ℝ q (poissonConvolutionL2 (by norm_num : (0 : ℝ) < 1) f)) :
    ∀ᵐ x, isotropicDirichletGlobalValue univ U x = 0 →
      rieszL2 (Complex.ofRealCLM.compLp q) x = 0 := by
  let S := isotropicPoissonTestStateTwo U q hTest
  let G := isotropicTwoH01 S
  have hValue : complexGlobalGraphCoordinateCLM 0 (G : H1amb univ) =
      isotropicEnergyValue 1 U.val :=
    (complexGlobalGraphCoordinate_isotropicTwoH01 S
      (isotropicDirichletGlobalValue univ U)
      (isotropicDirichlet_complexValue_eq MeasurableSet.univ U)).trans rfl
  have hFrequency := isotropicNormFourier_ae_of_regularizedEquation
    (isotropicEnergyValue 1 U.val) q
    (poissonGenerator_regularized_of_test_equations (by norm_num) U q hTest)
  have hv : ((G : H1amb univ) 0 : D → ℝ) =ᵐ[volume]
      isotropicDirichletGlobalValue univ U :=
    (isotropicTwoH01_value_ae S).trans (isotropicDirichletGlobalValue_ae U).symm
  have hz : ∀ᵐ x, ((G : H1amb univ) 0 x : ℝ) = 0 →
      ∀ i : Fin n, ((G : H1amb univ) i.succ x : ℝ) = 0 := by
    simpa only [Measure.restrict_univ] using
      ae_all_gradients_eq_zero_on_value_zero isOpen_univ G
  have hc : ∀ᵐ x, ∀ i : Fin n, rieszL2 (Complex.ofRealCLM.compLp q) x i =
      (((G : H1amb univ) i.succ x : ℝ) : ℂ) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [projectionCoordinateCLM_ae (rieszL2 (Complex.ofRealCLM.compLp q)) i,
      Lp.ext_iff.mp (rieszCoordinate_eq_gradient_of_norm_fourier G _ q hValue hFrequency i),
      complexGlobalGraphCoordinateCLM_ae i.succ (G : H1amb univ)] with x hr he hg
    exact hr.symm.trans (he.trans hg)
  filter_upwards [hv, hz, hc] with x hv hz hc
  intro hx
  ext i
  change rieszL2 (Complex.ofRealCLM.compLp q) x i = 0
  rw [hc i, hz (hv.trans hx) i, Complex.ofReal_zero]

end PartialBalayage.Linear
