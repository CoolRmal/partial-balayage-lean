/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierDirichletEnergy
public import PartialBalayage.Linear.PoissonHalfEnergyLimit
public import PartialBalayage.Linear.PoissonWeakRegularization

/-!
# The actual Poisson generator on genuine whole-space physical Dirichlet graphs

The exact Fourier-gradient identity gives finite first-order isotropic energy for every
actual whole-space `H01` graph. Its genuine Poisson generator has squared `L²` norm equal
to the physical Dirichlet energy and defines a bounded real linear map. This permits
compact-test equations to extend using the actual physical test-graph closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology FourierTransform
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal RealInnerProductSpace
open scoped Topology

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "H01ℝ" => H01 (univ : Set D)

/-- The actual global real value inclusion of a physical whole-space graph. -/
def h01RealValueCLM : H01ℝ →L[ℝ] L²ℝ :=
  zeroExtendL2CLM MeasurableSet.univ ∘L
    PiLp.proj 2 (fun _ : Fin (n + 1) ↦ L2D (univ : Set D)) 0 ∘L (H01 univ).subtypeL

/-- The true whole-space complex value of a physical real Dirichlet graph. -/
def h01ComplexValueCLM : H01ℝ →L[ℝ] L²ℂ :=
  complexGlobalGraphCoordinateCLM 0 ∘L (H01 univ).subtypeL

theorem h01ComplexValueCLM_eq_complexify (U : H01ℝ) :
    h01ComplexValueCLM U = Complex.ofRealCLM.compLp (h01RealValueCLM U) := rfl

theorem re_compLp_complexify (f : L²ℝ) :
    Complex.reCLM.compLp (Complex.ofRealCLM.compLp f) = f := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp (Complex.ofRealCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp f] with x hr hc
  rw [hr, hc, Complex.reCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_re]

/-- Actual physical first derivatives give genuine finite full isotropic first-order energy. -/
theorem fourierEnergy_two_h01ComplexValue_ne_top (U : H01ℝ) :
    fourierEnergy 2 (h01ComplexValueCLM U) ≠ ⊤ := by
  have he := fourierEnergy_two_complexGlobalGraphCoordinate_H01 U
  have hc : ENNReal.ofReal ((2 * Real.pi) ^ 2) ≠ 0 := by positivity
  intro htop
  have hmul := ENNReal.mul_eq_top.mpr (Or.inl ⟨hc, htop⟩)
  change ENNReal.ofReal ((2 * Real.pi) ^ 2) * fourierEnergy 2 (h01ComplexValueCLM U) = _ at he
  exact ENNReal.ofReal_ne_top (he.symm.trans hmul)

/-- The actual isotropic first-order state of a genuine physical Dirichlet graph. -/
def h01IsotropicStateTwo (U : H01ℝ) : IsotropicEnergySpace (X := D) (E := ℂ) 2 :=
  isotropicStateOfFiniteEnergy 2 (h01ComplexValueCLM U)
    (fourierEnergy_two_h01ComplexValue_ne_top U)

theorem isotropicEnergyValue_h01IsotropicStateTwo (U : H01ℝ) :
    isotropicEnergyValue 2 (h01IsotropicStateTwo U) = h01ComplexValueCLM U := rfl

/-- The actual complex Poisson generator on the original physical graph. -/
def h01PoissonGenerator (U : H01ℝ) : L²ℂ := poissonGenerator (h01IsotropicStateTwo U)

/-- Its true Fourier representative is the full isotropic norm multiplier. -/
theorem fourier_h01PoissonGenerator_ae (U : H01ℝ) :
    ∀ᵐ ξ, (𝓕 (h01PoissonGenerator U) : L²ℂ) ξ =
      ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) • (𝓕 (h01ComplexValueCLM U) : L²ℂ) ξ :=
  fourier_poissonGenerator_ae (h01IsotropicStateTwo U)

/-- The genuine Poisson generator's squared norm equals the physical Dirichlet energy. -/
theorem norm_h01PoissonGenerator_sq (U : H01ℝ) :
    ‖h01PoissonGenerator U‖ ^ 2 = laplaceBilin univ U U := by
  have hnorm : ‖h01PoissonGenerator U‖ =
      2 * Real.pi * ‖isotropicEnergyData 2 (h01IsotropicStateTwo U)‖ := by
    change ‖(Lp.fourierTransformₗᵢ D ℂ).symm
      ((2 * Real.pi : ℂ) • isotropicEnergyData 2 (h01IsotropicStateTwo U))‖ = _
    rw [(Lp.fourierTransformₗᵢ D ℂ).symm.norm_map, norm_smul]
    have hc : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hc]
  have he := fourierEnergy_two_complexGlobalGraphCoordinate_H01 U
  change ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    fourierEnergy 2 (isotropicEnergyValue 2 (h01IsotropicStateTwo U)) = _ at he
  rw [← isotropicEnergyData_enorm_sq 2 (h01IsotropicStateTwo U)] at he
  have hr := congrArg ENNReal.toReal he
  have hLap : 0 ≤ laplaceBilin univ U U := by
    rw [laplaceBilin_self]
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ← ofReal_norm,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal hLap] at hr
  rw [hnorm, mul_pow]
  exact hr

theorem h01PoissonGenerator_add (U V : H01ℝ) :
    h01PoissonGenerator (U + V) = h01PoissonGenerator U + h01PoissonGenerator V := by
  apply (Lp.fourierTransformₗᵢ D ℂ).injective
  change 𝓕 (h01PoissonGenerator (U + V)) = 𝓕 (h01PoissonGenerator U + h01PoissonGenerator V)
  rw [FourierTransform.fourier_add]
  have hv : 𝓕 (h01ComplexValueCLM (U + V)) =
      𝓕 (h01ComplexValueCLM U) + 𝓕 (h01ComplexValueCLM V) := by
    rw [map_add, FourierTransform.fourier_add]
  apply Lp.ext
  filter_upwards [fourier_h01PoissonGenerator_ae (U + V),
    fourier_h01PoissonGenerator_ae U, fourier_h01PoissonGenerator_ae V,
    Lp.coeFn_add (𝓕 (h01PoissonGenerator U)) (𝓕 (h01PoissonGenerator V)),
    Lp.coeFn_add (𝓕 (h01ComplexValueCLM U)) (𝓕 (h01ComplexValueCLM V))]
      with ξ hsum hU hV hgs hvs
  rw [hsum, hv, hvs, Pi.add_apply, smul_add, hgs, Pi.add_apply, hU, hV]

theorem h01PoissonGenerator_smul (c : ℝ) (U : H01ℝ) :
    h01PoissonGenerator (c • U) = c • h01PoissonGenerator U := by
  apply (Lp.fourierTransformₗᵢ D ℂ).injective
  change 𝓕 (h01PoissonGenerator (c • U)) = 𝓕 (c • h01PoissonGenerator U)
  have hFs (f : L²ℂ) : 𝓕 (c • f) = c • 𝓕 f :=
    ((Lp.fourierTransformₗᵢ D ℂ).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars
      ℝ).map_smul c f
  rw [hFs]
  have hv : 𝓕 (h01ComplexValueCLM (c • U)) = c • 𝓕 (h01ComplexValueCLM U) :=
    by rw [map_smul, hFs]
  apply Lp.ext
  filter_upwards [fourier_h01PoissonGenerator_ae (c • U), fourier_h01PoissonGenerator_ae U,
    Lp.coeFn_smul c (𝓕 (h01PoissonGenerator U)),
    Lp.coeFn_smul c (𝓕 (h01ComplexValueCLM U))] with ξ hc hU hgs hvs
  rw [hc, hv, hvs, Pi.smul_apply, hgs, Pi.smul_apply, hU, smul_comm]

/-- The actual full-norm generator is bounded by the physical graph norm. -/
theorem norm_h01PoissonGenerator_le (U : H01ℝ) : ‖h01PoissonGenerator U‖ ≤ ‖U‖ := by
  have he : laplaceBilin univ U U ≤ ‖U‖ ^ 2 := by
    have hg := PiLp.norm_sq_eq_of_L2
      (fun _ : Fin (n + 1) ↦ L2D (univ : Set D)) U.val
    rw [Fin.sum_univ_succ] at hg
    calc
      _ = ∑ i : Fin n, ‖U.val i.succ‖ ^ 2 := laplaceBilin_self _ _
      _ ≤ ‖U.val‖ ^ 2 := by rw [hg]; exact le_add_of_nonneg_left (sq_nonneg _)
      _ = _ := rfl
  rw [← norm_h01PoissonGenerator_sq] at he
  nlinarith [norm_nonneg U, norm_nonneg (h01PoissonGenerator U)]

/-- The genuine complex Poisson generator as a bounded real linear map on physical graphs. -/
def h01PoissonGeneratorCLM : H01ℝ →L[ℝ] L²ℂ :=
  LinearMap.mkContinuous
    { toFun := h01PoissonGenerator
      map_add' := h01PoissonGenerator_add
      map_smul' := h01PoissonGenerator_smul }
    1 (fun U ↦ by
      change ‖h01PoissonGenerator U‖ ≤ 1 * ‖U‖
      rw [one_mul]
      exact norm_h01PoissonGenerator_le U)

/-- Its actual real part is the scalar real Poisson generator used in compact-test passage. -/
def h01PoissonRealGeneratorCLM : H01ℝ →L[ℝ] L²ℝ :=
  Complex.reCLM.compLpL 2 volume ∘L h01PoissonGeneratorCLM

/-- The true real Poisson quotient of the actual physical value tends to its actual generator. -/
theorem tendsto_h01PoissonRealQuotient (U : H01ℝ) :
    Tendsto (fun t : ℝ ↦ if ht : 0 < t then poissonRealQuotientL2CLM ht (h01RealValueCLM U)
      else 0) (𝓝[>] 0) (𝓝 (h01PoissonRealGeneratorCLM U)) := by
  have hlim := (Complex.reCLM.compLpL 2 (volume : Measure D)).continuous.tendsto
    (poissonGenerator (h01IsotropicStateTwo U)) |>.comp
      (tendsto_poissonDifferenceQuotient (h01IsotropicStateTwo U))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  change Complex.reCLM.compLp (poissonDifferenceQuotient t (h01IsotropicStateTwo U)) =
    if ht : 0 < t then poissonRealQuotientL2CLM ht (h01RealValueCLM U) else 0
  rw [dite_eq_left ht, poissonDifferenceQuotient, dite_eq_left ht]
  change Complex.reCLM.compLp (poissonQuotientL2 ht (h01ComplexValueCLM U)) = _
  rw [h01ComplexValueCLM_eq_complexify, poissonQuotientL2_complexify, re_compLp_complexify]
  rfl

end PartialBalayage.Linear
