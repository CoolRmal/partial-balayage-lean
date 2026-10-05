/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonGeneratorReality
public import PartialBalayage.Linear.IsotropicDirichletCoercivity

/-!
# Genuine Poisson tests for the whole-space half-order equation

Every actual real L2 input gives a real whole-space half-order test by spatial
Poisson regularization. The half-order form is the actual regularized generator pairing.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set Filter
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "WholeState" => IsotropicDirichletState (univ : Set D)

/-- The actual complex value of a real Dirichlet state is its complexified real value. -/
theorem isotropicDirichlet_complexValue_eq {Ω : Set D} (hΩ : MeasurableSet Ω)
    (U : IsotropicDirichletState Ω) :
    isotropicEnergyValue 1 U.val =
      Complex.ofRealCLM.compLp (isotropicDirichletGlobalValue Ω U) := by
  apply Lp.ext
  filter_upwards [isotropicDirichlet_complexValue_ae hΩ U,
    Complex.ofRealCLM.coeFn_compLp (isotropicDirichletGlobalValue Ω U)] with x hx hc
  simpa only [Complex.ofRealCLM_apply] using hx.trans hc.symm

/-- An actually real-valued half-order state is a genuine whole-space real state. -/
def isotropicWholeStateOfRealValue (U : IsotropicScalarEnergy (n := n) 1) (f : L²ℝ)
    (hU : isotropicEnergyValue 1 U = Complex.ofRealCLM.compLp f) : WholeState :=
  ⟨U, (mem_isotropicRealSupported_iff MeasurableSet.univ U).mpr (by
    constructor
    · rw [hU]
      filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
      simp only [hx, Complex.ofRealCLM_apply, Complex.ofReal_im]
    · exact Eventually.of_forall fun _ h ↦ False.elim (h (mem_univ _)))⟩

/-- The actual spatial Poisson average constructs a real whole-space energy test. -/
def poissonRealHalfTest {t : ℝ} (ht : 0 < t) (f : L²ℝ) : WholeState :=
  isotropicWholeStateOfRealValue
    (isotropicHalfStateOfTwo (poissonSmoothedStateTwo ht (Complex.ofRealCLM.compLp f)))
    (poissonConvolutionL2 ht f) (by
      rw [isotropicEnergyValue_isotropicHalfStateOfTwo,
        isotropicEnergyValue_poissonSmoothedStateTwo, poissonConvolutionL2_compLp ht])

/-- Its actual global real value is the original spatial Poisson average. -/
theorem isotropicDirichletGlobalValue_poissonRealHalfTest {t : ℝ} (ht : 0 < t)
    (f : L²ℝ) :
    isotropicDirichletGlobalValue univ (poissonRealHalfTest ht f) =
      poissonConvolutionL2 ht f := by
  have h := isotropicDirichlet_complexValue_eq MeasurableSet.univ
    (poissonRealHalfTest ht f)
  have hv : isotropicEnergyValue 1 (poissonRealHalfTest ht f).val =
      Complex.ofRealCLM.compLp (poissonConvolutionL2 ht f) := by
    change isotropicEnergyValue 1
      (isotropicHalfStateOfTwo (poissonSmoothedStateTwo ht (Complex.ofRealCLM.compLp f))) = _
    rw [isotropicEnergyValue_isotropicHalfStateOfTwo,
      isotropicEnergyValue_poissonSmoothedStateTwo, poissonConvolutionL2_compLp ht]
  rw [hv] at h
  apply Lp.ext
  filter_upwards [Lp.ext_iff.mp h,
    Complex.ofRealCLM.coeFn_compLp (poissonConvolutionL2 ht f),
    Complex.ofRealCLM.coeFn_compLp
      (isotropicDirichletGlobalValue univ (poissonRealHalfTest ht f))]
    with x hx hf hg
  have he := congrArg Complex.re hx
  simpa only [hf, hg, Complex.ofRealCLM_apply, Complex.ofReal_re] using he.symm

/-- The real inner product of actual complex L2 classes is their complex pairing's real part. -/
theorem real_inner_complexLp (f g : L²ℂ) :
    inner ℝ f g = (inner ℂ f g).re := by
  have hr := Complex.reCLM.integral_comp_comm (L2.integrable_inner f g)
  simp only [Complex.reCLM_apply] at hr
  rw [L2.inner_def, L2.inner_def, ← hr]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ ↦ rfl

/-- The actual half-order form against a Poisson test is the genuine smoothed generator. -/
theorem isotropicDirichletForm_poissonRealHalfTest {t : ℝ} (ht : 0 < t)
    (U : WholeState) (f : L²ℝ) :
    isotropicDirichletForm univ U (poissonRealHalfTest ht f) =
      (inner ℂ (poissonGenerator (poissonSmoothedStateTwo ht
        (isotropicEnergyValue 1 U.val))) (Complex.ofRealCLM.compLp f)).re := by
  rw [isotropicDirichletForm_apply, real_inner_complexLp]
  change 2 * Real.pi * (inner ℂ (isotropicEnergyData 1 U.val)
    (isotropicEnergyData 1 (isotropicHalfStateOfTwo
      (poissonSmoothedStateTwo ht (Complex.ofRealCLM.compLp f))))).re = _
  have h := congrArg Complex.re (inner_isotropicHalfDataOfTwo U.val
    (poissonSmoothedStateTwo ht (Complex.ofRealCLM.compLp f)))
  norm_num [Complex.mul_re, Complex.mul_im] at h
  rw [h, inner_poissonSmoothedGenerator ht]

/-- The genuine weak half-order equation identifies every regularized spatial generator. -/
theorem poissonGenerator_regularized_weakPDE {t : ℝ} (ht : 0 < t)
    (U : WholeState) (q : L²ℝ)
    (hPDE : ∀ V : WholeState, isotropicDirichletForm univ U V =
      inner ℝ q (isotropicDirichletGlobalValue univ V)) :
    poissonGenerator (poissonSmoothedStateTwo ht (isotropicEnergyValue 1 U.val)) =
      Complex.ofRealCLM.compLp (poissonConvolutionL2 ht q) := by
  let G := poissonGenerator (poissonSmoothedStateTwo ht (isotropicEnergyValue 1 U.val))
  let g := Complex.reCLM.compLp G
  have hvalue : isotropicEnergyValue 2
      (poissonSmoothedStateTwo ht (isotropicEnergyValue 1 U.val)) =
      Complex.ofRealCLM.compLp
        (poissonConvolutionL2 ht (isotropicDirichletGlobalValue univ U)) := by
    rw [isotropicEnergyValue_poissonSmoothedStateTwo,
      isotropicDirichlet_complexValue_eq MeasurableSet.univ,
      poissonConvolutionL2_compLp ht]
  have hg : Complex.ofRealCLM.compLp g = G :=
    complexify_re_compLp_of_im_eq_zero G
      (im_compLp_poissonGenerator_eq_zero _ _ hvalue)
  have he : g = poissonConvolutionL2 ht q := by
    apply ext_inner_right ℝ
    intro f
    have h := hPDE (poissonRealHalfTest ht f)
    rw [isotropicDirichletGlobalValue_poissonRealHalfTest,
      isotropicDirichletForm_poissonRealHalfTest] at h
    change (inner ℂ G (Complex.ofRealCLM.compLp f)).re = _ at h
    rw [← hg, re_inner_complexifyL2] at h
    have hs := inner_poissonConvolutionL2 ht (Complex.ofRealCLM.compLp q)
      (Complex.ofRealCLM.compLp f)
    rw [poissonConvolutionL2_compLp ht, poissonConvolutionL2_compLp ht] at hs
    have hr := congrArg Complex.re hs
    rw [re_inner_complexifyL2, re_inner_complexifyL2] at hr
    exact h.trans hr
  exact hg.symm.trans (congrArg (fun f : L²ℝ ↦ Complex.ofRealCLM.compLp f) he)

end PartialBalayage.Linear
