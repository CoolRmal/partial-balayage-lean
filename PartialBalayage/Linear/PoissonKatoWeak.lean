/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonKatoTest
public import PartialBalayage.Linear.PoissonSelfAdjoint
public import PartialBalayage.Linear.PoissonPostcomposition

/-!
# The true weak isotropic Kato inequality

Actual Poisson self-adjointness moves the scalar norm defect onto the test. Strong generator
convergence then proves the weak Kato inequality, without any generator-domain assumption
on the pointwise norm of the potential.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance poissonKatoWeakRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonKatoWeakScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := E) 2
local notation "H¹ℂ" => IsotropicEnergySpace (X := D) (E := ℂ) 2

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- Complexifying real `L²` inputs preserves their actual inner product. -/
theorem re_inner_complexifyL2 (f g : L²ℝ) :
    (inner ℂ (Complex.ofRealCLM.compLp f) (Complex.ofRealCLM.compLp g)).re =
      inner ℝ f g := by
  have hire := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner (Complex.ofRealCLM.compLp f) (Complex.ofRealCLM.compLp g))
  simp only [Complex.reCLM_apply] at hire
  rw [L2.inner_def, L2.inner_def, ← hire]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f, Complex.ofRealCLM.coeFn_compLp g]
    with x hf hg
  rw [hf, hg, Complex.ofRealCLM_apply, Complex.ofRealCLM_apply]
  rw [Real.inner_apply]
  simp only [RCLike.inner_apply, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The genuine spatial Poisson quotient commutes with actual complexification. -/
theorem poissonQuotientL2_complexify {t : ℝ} (ht : 0 < t) (f : L²ℝ) :
    poissonQuotientL2 ht (Complex.ofRealCLM.compLp f) =
      Complex.ofRealCLM.compLp (t⁻¹ • (f - poissonConvolutionL2 ht f)) := by
  rw [poissonQuotientL2, poissonConvolutionL2_compLp ht]
  have hsmul := (Complex.ofRealCLM.compLpL 2 (volume : Measure D)).map_smul
    t⁻¹ (f - poissonConvolutionL2 ht f)
  have hsub := (Complex.ofRealCLM.compLpL 2 (volume : Measure D)).map_sub
    f (poissonConvolutionL2 ht f)
  change (t⁻¹ : ℂ) • (Complex.ofRealCLM.compLp f -
    Complex.ofRealCLM.compLp (poissonConvolutionL2 ht f)) =
      (Complex.ofRealCLM.compLpL 2 volume) (t⁻¹ • (f - poissonConvolutionL2 ht f))
  rw [hsmul, hsub]
  change (t⁻¹ : ℂ) • (Complex.ofRealCLM.compLp f -
    Complex.ofRealCLM.compLp (poissonConvolutionL2 ht f)) =
      (t⁻¹ : ℝ) • (Complex.ofRealCLM.compLp f -
        Complex.ofRealCLM.compLp (poissonConvolutionL2 ht f))
  rw [← Complex.ofReal_inv, Complex.coe_smul]
  rfl

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
private theorem poisson_kato_test_transfer {t : ℝ} (ht : 0 < t) (f : L²)
    (φ : L²ℝ) (Φ : H¹ℂ)
    (hΦ : isotropicEnergyValue 2 Φ = Complex.ofRealCLM.compLp φ) :
    inner ℝ φ (poissonNormDefectL2 ht f) =
      (inner ℂ (Complex.ofRealCLM.compLp (poissonNormL2 f))
        (poissonDifferenceQuotient t Φ)).re := by
  rw [poissonDifferenceQuotient, dite_eq_left ht]
  change _ = (inner ℂ (Complex.ofRealCLM.compLp (poissonNormL2 f))
    (poissonQuotientL2 ht (isotropicEnergyValue 2 Φ))).re
  rw [hΦ, inner_poissonQuotientL2 ht]
  have hsymm := inner_re_symm (𝕜 := ℂ)
    (poissonQuotientL2 ht (Complex.ofRealCLM.compLp (poissonNormL2 f)))
    (Complex.ofRealCLM.compLp φ)
  change _ = RCLike.re (inner ℂ
    (poissonQuotientL2 ht (Complex.ofRealCLM.compLp (poissonNormL2 f)))
    (Complex.ofRealCLM.compLp φ))
  rw [hsymm, poissonQuotientL2_complexify ht, RCLike.re_eq_complex_re,
    re_inner_complexifyL2]
  rfl

/-- The actual isotropic generator satisfies weak Kato against genuine real nonnegative tests. -/
theorem poisson_generator_weak_kato (U : H¹) (φ : L²ℝ) (Φ : H¹ℂ) (W : L²)
    (hΦ : isotropicEnergyValue 2 Φ = Complex.ofRealCLM.compLp φ)
    (hw : ∀ᵐ x, ‖W x‖ ≤ φ x)
    (hs : ∀ᵐ x, (inner ℂ (W x) (isotropicEnergyValue 2 U x)).re =
      φ x * ‖isotropicEnergyValue 2 U x‖) :
    (inner ℂ (Complex.ofRealCLM.compLp (poissonNormL2 (isotropicEnergyValue 2 U)))
      (poissonGenerator Φ)).re ≤ (inner ℂ W (poissonGenerator U)).re := by
  have hleft := tendsto_poissonGenerator_inner_test Φ
    (Complex.ofRealCLM.compLp (poissonNormL2 (isotropicEnergyValue 2 U)))
  apply le_of_tendsto_of_tendsto hleft (tendsto_poissonGenerator_inner_test U W)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← poisson_kato_test_transfer ht (isotropicEnergyValue 2 U) φ Φ hΦ]
  exact poisson_kato_L2_test ht U φ W hw hs

end PartialBalayage.Linear
