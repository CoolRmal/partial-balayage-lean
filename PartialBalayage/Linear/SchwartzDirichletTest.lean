/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.SobolevUnivDensity
public import PartialBalayage.Linear.SobolevDistributionGradient
public import PartialBalayage.Linear.DirichletTestClosure

/-!
# Genuine Schwartz Dirichlet tests

The classical Schwartz value and first derivatives form an actual weak graph. Whole-space
density places it in the genuine `H01` closure. Actual weak Dirichlet equations can therefore
be tested against Schwartz functions, giving the genuine tempered-distribution Laplacian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter LineDeriv
open CenteredMaximal.Ball.DirichletSobolev
open scoped SchwartzMap LineDeriv Laplacian RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)

/-- Schwartz functions are genuinely square integrable for the all-space graph measure. -/
theorem schwartzReal_memLp_univ (φ : 𝓢(X, ℝ)) :
    MemLp φ 2 (volume.restrict (univ : Set X)) := by
  simpa only [Measure.restrict_univ] using φ.memLp 2 volume

/-- The actual `L²` value and first-derivative graph of a real Schwartz function. -/
def schwartzRealGraph (φ : 𝓢(X, ℝ)) : H1amb (univ : Set X) :=
  WithLp.toLp 2 (Fin.cons ((schwartzReal_memLp_univ φ).toLp φ)
    (fun i : Fin d ↦ (schwartzReal_memLp_univ
      (∂_{EuclideanSpace.single i (1 : ℝ)} φ)).toLp
        (∂_{EuclideanSpace.single i (1 : ℝ)} φ : 𝓢(X, ℝ))))

/-- The actual Schwartz graph value agrees almost everywhere with its classical value. -/
theorem schwartzRealGraph_value_ae (φ : 𝓢(X, ℝ)) :
    schwartzRealGraph φ 0 =ᵐ[volume] φ := by
  simpa only [schwartzRealGraph, PiLp.toLp_apply, Fin.cons_zero, Measure.restrict_univ]
    using (schwartzReal_memLp_univ φ).coeFn_toLp

/-- The actual Schwartz graph gradients agree almost everywhere with classical derivatives. -/
theorem schwartzRealGraph_partial_ae (φ : 𝓢(X, ℝ)) (i : Fin d) :
    schwartzRealGraph φ i.succ =ᵐ[volume] partialD i φ := by
  have h := (schwartzReal_memLp_univ (∂_{EuclideanSpace.single i (1 : ℝ)} φ)).coeFn_toLp
  simp only [Measure.restrict_univ] at h
  simp only [schwartzRealGraph, PiLp.toLp_apply, Fin.cons_succ]
  filter_upwards [h] with x hx
  exact hx.trans (SchwartzMap.lineDerivOp_apply_eq_fderiv _ φ x)

/-- Classical Schwartz integration by parts gives the genuine weak graph constraints. -/
theorem schwartzRealGraph_mem_W12 (φ : 𝓢(X, ℝ)) : schwartzRealGraph φ ∈ W12 univ := by
  rw [mem_W12_iff]
  intro θ hθ i
  let ψ : 𝓢(X, ℝ) := hθ.2.1.toSchwartzMap hθ.1
  rw [L2.inner_def, L2.inner_def, setIntegral_univ, setIntegral_univ]
  have hθ0 : hθ.testCls =ᵐ[volume] θ := by
    simpa only [IsTestFn.testCls, Measure.restrict_univ] using hθ.mem_lp.coeFn_toLp
  have hθi : hθ.partialCls i =ᵐ[volume] partialD i θ := by
    simpa only [IsTestFn.partialCls, Measure.restrict_univ]
      using (hθ.memLp_partialD i).coeFn_toLp
  have hleft : (∫ x, inner ℝ (hθ.partialCls i x) (schwartzRealGraph φ 0 x)) =
      ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} ψ) x * φ x := by
    apply integral_congr_ae
    filter_upwards [hθi, schwartzRealGraph_value_ae φ] with x hi h0
    simp only [Real.inner_apply, hi, h0, SchwartzMap.lineDerivOp_apply_eq_fderiv, partialD]
    rfl
  have hright : (∫ x, inner ℝ (hθ.testCls x) (schwartzRealGraph φ i.succ x)) =
      ∫ x, ψ x * (∂_{EuclideanSpace.single i (1 : ℝ)} φ) x := by
    apply integral_congr_ae
    filter_upwards [hθ0, schwartzRealGraph_partial_ae φ i] with x h0 hi
    simp only [Real.inner_apply, hi, h0, SchwartzMap.lineDerivOp_apply_eq_fderiv, partialD]
    rfl
  rw [hleft, hright]
  have h := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume)
    ψ φ (EuclideanSpace.single i (1 : ℝ))
  linarith

/-- The actual Schwartz graph belongs to the genuine compact-test Dirichlet closure. -/
theorem schwartzRealGraph_mem_H01 (φ : 𝓢(X, ℝ)) : schwartzRealGraph φ ∈ H01 univ :=
  mem_H01_univ_of_mem_W12 (schwartzRealGraph_mem_W12 φ)

/-- A genuine whole-space Dirichlet test obtained from a real Schwartz function. -/
def schwartzDirichletTest (φ : 𝓢(X, ℝ)) : H01 (univ : Set X) :=
  ⟨schwartzRealGraph φ, schwartzRealGraph_mem_H01 φ⟩

/-- Actual weak Dirichlet equations hold for all classical real Schwartz value-gradient tests. -/
theorem schwartz_gradient_pairing_of_H01_equation
    (U : H01 (univ : Set X)) (g : L2D (univ : Set X))
    (hpde : ∀ W : H01 (univ : Set X),
      laplaceBilin univ U W = inner ℝ g ((W : H1amb univ) 0)) (φ : 𝓢(X, ℝ)) :
    (∑ i : Fin d, ∫ x, partialD i φ x * (U : H1amb (univ : Set X)) i.succ x) =
      ∫ x, φ x * g x := by
  have h := hpde (schwartzDirichletTest φ)
  simp only [laplaceBilin_apply, schwartzDirichletTest] at h
  have hpartials i : inner ℝ ((U : H1amb (univ : Set X)) i.succ) (schwartzRealGraph φ i.succ) =
      ∫ x, partialD i φ x * (U : H1amb (univ : Set X)) i.succ x := by
    rw [L2.inner_def, setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [schwartzRealGraph_partial_ae φ i] with x hx
    simp only [Real.inner_apply, hx, mul_comm]
  have hvalue : inner ℝ g (schwartzRealGraph φ 0) = ∫ x, φ x * g x := by
    rw [L2.inner_def, setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [schwartzRealGraph_value_ae φ] with x hx
    simp only [Real.inner_apply, hx, mul_comm]
  simp only [hpartials, hvalue] at h
  exact h

/-- A real linear output map commutes with classical Schwartz coordinate differentiation. -/
theorem partialD_schwartz_postcomp (φ : 𝓢(X, ℂ)) (L : ℂ →L[ℝ] ℝ) (i : Fin d) (x : X) :
    partialD i (φ.postcompCLM L) x = L ((∂_{EuclideanSpace.single i (1 : ℝ)} φ) x) := by
  rw [partialD, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (L ∘ φ) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_comp x L.differentiableAt φ.differentiableAt, ContinuousLinearMap.fderiv]
  rfl

private theorem integral_complex_real_mul_map (L : ℂ →L[ℝ] ℝ) (φ : 𝓢(X, ℂ))
    (a : L2D (univ : Set X))
    (A : Lp ℂ 2 (volume : Measure X)) (ha : A =ᵐ[volume] fun x ↦ (a x : ℂ)) :
    L (∫ x, φ x * A x) = ∫ x, L (φ x) * a x := by
  have hint : Integrable (fun x ↦ φ x * A x) volume :=
    (φ.memLp 2 volume).integrable_mul (Lp.memLp A)
  rw [← L.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  rw [hx, mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]

/-- Genuine scalar `L²` complexification after removal of the whole-space restriction. -/
def complexUnivL2 (g : L2D (univ : Set X)) : Lp ℂ 2 (volume : Measure X) :=
  Complex.ofRealCLM.compLp (zeroExtendL2 MeasurableSet.univ g)

/-- The actual complexified forcing agrees almost everywhere with the original real forcing. -/
theorem complexUnivL2_ae (g : L2D (univ : Set X)) :
    complexUnivL2 g =ᵐ[volume] fun x ↦ (g x : ℂ) := by
  change Complex.ofRealCLM.compLp (zeroExtendL2 MeasurableSet.univ g) =ᵐ[volume] _
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (zeroExtendL2 MeasurableSet.univ g),
    zeroExtendL2_ae (μ := volume) MeasurableSet.univ g] with x hc hr
  simp only [indicator_univ] at hr
  rw [hc, hr]
  rfl

/-- Genuine Dirichlet equations extend to the complex Schwartz gradient pairing. -/
theorem complex_schwartz_gradient_pairing_of_H01_equation
    (U : H01 (univ : Set X)) (g : L2D (univ : Set X))
    (hpde : ∀ W : H01 (univ : Set X),
      laplaceBilin univ U W = inner ℝ g ((W : H1amb univ) 0)) (φ : 𝓢(X, ℂ)) :
    (∑ i : Fin d, ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} φ) x *
      complexGlobalGraphCoordinateCLM i.succ (U : H1amb (univ : Set X)) x) =
      ∫ x, φ x * complexUnivL2 g x := by
  have hcomponent (L : ℂ →L[ℝ] ℝ) :
      L (∑ i : Fin d, ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} φ) x *
        complexGlobalGraphCoordinateCLM i.succ (U : H1amb (univ : Set X)) x) =
        L (∫ x, φ x * complexUnivL2 g x) := by
    rw [map_sum]
    simp_rw [integral_complex_real_mul_map L _ _ _
      (complexGlobalGraphCoordinateCLM_ae _ (U : H1amb (univ : Set X))),
      integral_complex_real_mul_map L φ g _ (complexUnivL2_ae g)]
    simpa only [partialD_schwartz_postcomp, SchwartzMap.postcompCLM_apply] using
      schwartz_gradient_pairing_of_H01_equation U g hpde (φ.postcompCLM L)
  exact Complex.ext (hcomponent Complex.reCLM) (hcomponent Complex.imCLM)

/-- A genuine all-space Dirichlet equation gives the actual represented tempered Laplacian. -/
theorem laplacian_complexGlobalGraphCoordinate_of_H01_equation
    (U : H01 (univ : Set X)) (g : L2D (univ : Set X))
    (hpde : ∀ W : H01 (univ : Set X),
      laplaceBilin univ U W = inner ℝ g ((W : H1amb univ) 0)) :
    Δ (Lp.toTemperedDistribution
      (complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb (univ : Set X)))) =
      -Lp.toTemperedDistribution (complexUnivL2 g) := by
  rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp_rw [EuclideanSpace.basisFun_apply, lineDeriv_complexGlobalGraphCoordinate_H01]
  ext φ
  simp only [sum_apply, TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, smul_eq_mul, neg_apply, neg_mul,
    integral_neg, Finset.sum_neg_distrib]
  exact congrArg Neg.neg (complex_schwartz_gradient_pairing_of_H01_equation U g hpde φ)

/-- A genuine compact-test equation gives the actual tempered-distribution Laplacian. -/
theorem laplacian_complexGlobalGraphCoordinate_of_test_equation
    (U : H01 (univ : Set X)) (g : L2D (univ : Set X))
    (htest : ∀ (φ : X → ℝ) (hφ : IsTestFn univ φ),
      laplaceBilin univ U hφ.toH01 = inner ℝ g hφ.testCls) :
    Δ (Lp.toTemperedDistribution
      (complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb (univ : Set X)))) =
      -Lp.toTemperedDistribution (complexUnivL2 g) :=
  laplacian_complexGlobalGraphCoordinate_of_H01_equation U g
    (laplaceBilin_eq_inner_of_test_equation U g htest)

end PartialBalayage.Linear
