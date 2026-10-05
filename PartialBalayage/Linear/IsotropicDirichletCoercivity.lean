/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.IsotropicDirichletSpace
public import PartialBalayage.Linear.FourierCoercivity
public import PartialBalayage.Linear.DirichletDual
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual finite-domain coercivity of the isotropic half-order operator

Finite physical support gives an actual `L¹` bound by the `L²` norm. The genuine low/high
Fourier estimate then makes the half-order energy coercive on every measurable domain of
finite volume in positive dimension. Its Riesz representative is the actual positive
Dirichlet operator used in the signed dual obstacle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace Metric
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)

/-- Finite support makes a genuine global `L²` class integrable. -/
theorem integrable_L2_of_finite_support {Ω : Set D} (hΩ : MeasurableSet Ω)
    (hfin : volume Ω ≠ ⊤) (f : L²ℂ) (hs : ∀ᵐ x, x ∉ Ω → f x = 0) :
    Integrable (f : D → ℂ) := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hi := ((Lp.memLp f).mono_measure
    (Measure.restrict_le_self (μ := (volume : Measure D)) (s := Ω))).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply ((integrable_indicator_iff hΩ).mpr hi).congr
  filter_upwards [hs] with x hx
  by_cases hxo : x ∈ Ω
  · exact indicator_of_mem hxo _
  · rw [indicator_of_notMem hxo, hx hxo]

/-- Cauchy--Schwarz on the actual norm representative gives the finite-support mass bound. -/
theorem integral_norm_L2_sq_le_of_finite_support {Ω : Set D} (hΩ : MeasurableSet Ω)
    (hfin : volume Ω ≠ ⊤) (f : L²ℂ) (hs : ∀ᵐ x, x ∉ Ω → f x = 0) :
    (∫ x, ‖f x‖) ^ 2 ≤ (volume Ω).toReal * ‖f‖ ^ 2 := by
  let q := poissonNormL2 f
  let c := indicatorConstLp 2 hΩ hfin (1 : ℝ)
  have hq : ‖q‖ = ‖f‖ := by
    change ‖poissonNormL2 f‖ = ‖f‖
    rw [poissonNormL2, Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f)]
    exact (Lp.norm_def f).symm
  have hc : ‖c‖ = Real.sqrt (volume Ω).toReal := by
    simp [c, norm_indicatorConstLp, measureReal_def, Real.sqrt_eq_rpow]
  have he : ⟪q, c⟫ = ∫ x, ‖f x‖ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [poissonNormL2_ae f, indicatorConstLp_coeFn (p := 2)
      (hs := hΩ) (hμs := hfin) (c := (1 : ℝ)), hs] with x hq hc hx
    rw [hq, hc, Real.inner_apply]
    by_cases hxo : x ∈ Ω
    · simp only [indicator_of_mem hxo, mul_one]
    · simp only [indicator_of_notMem hxo, mul_zero, hx hxo, norm_zero]
  have hle := real_inner_le_norm q c
  rw [he, hq, hc] at hle
  have hM : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg (fun x ↦ norm_nonneg (f x))
  nlinarith [Real.sq_sqrt (volume Ω).toReal_nonneg,
    mul_nonneg (norm_nonneg f) (Real.sqrt_nonneg (volume Ω).toReal)]

/-- The weighted Fourier coordinate has the genuine finite real energy. -/
theorem isotropicDirichlet_fourierEnergy_toReal {Ω : Set D}
    (U : IsotropicDirichletState (n := n) Ω) :
    (fourierEnergy 1 (isotropicEnergyValue 1 U.val)).toReal =
      ‖isotropicDirichletData (n := n) Ω U‖ ^ 2 := by
  rw [← isotropicEnergyData_enorm_sq, ← ofReal_norm, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (norm_nonneg _)]
  rfl

/-- Finite-domain isotropic energy controls the full actual graph norm. -/
theorem exists_isotropicDirichlet_graph_energy_bound (hn : 0 < n)
    {Ω : Set D} (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : IsotropicDirichletState (n := n) Ω,
      ‖U‖ ^ 2 ≤ C * ‖isotropicDirichletData (n := n) Ω U‖ ^ 2 := by
  have hdim : 0 < Module.finrank ℝ D := by simpa using hn
  obtain ⟨R, hR, hsmall⟩ := exists_small_fourier_radius (X := D) hdim
    (κ := 1) (F := Real.sqrt (volume Ω).toReal) zero_lt_one
    (Real.sqrt_nonneg _)
  have hv : (volume Ω).toReal * (volume (closedBall (0 : D) R)).toReal ≤ 1 / 4 := by
    have h₁ := Real.sq_sqrt (volume Ω).toReal_nonneg
    have h₂ := Real.sq_sqrt (volume (closedBall (0 : D) R)).toReal_nonneg
    have hp := mul_nonneg (Real.sqrt_nonneg (volume Ω).toReal)
      (Real.sqrt_nonneg (volume (closedBall (0 : D) R)).toReal)
    nlinarith
  refine ⟨1 + 2 * R ^ (-1 : ℝ), by positivity, fun U ↦ ?_⟩
  have hs := (mem_isotropicRealSupported_iff hΩ U.val).mp U.property |>.2
  have hi := integrable_L2_of_finite_support hΩ hfin (isotropicEnergyValue 1 U.val) hs
  have hsplit := norm_sq_le_fourier_energy_split (isotropicEnergyValue 1 U.val) hi
    (α := 1) (by norm_num) hR (fourierEnergy_ne_top 1 U.val)
  have hm := integral_norm_L2_sq_le_of_finite_support hΩ hfin
    (isotropicEnergyValue 1 U.val) hs
  have hmass := mul_le_mul_of_nonneg_right hm
    (volume (closedBall (0 : D) R)).toReal_nonneg
  have hsmall' := mul_le_mul_of_nonneg_right hv (sq_nonneg ‖isotropicEnergyValue 1 U.val‖)
  rw [isotropicDirichlet_fourierEnergy_toReal] at hsplit
  have hnEq : ‖U‖ ^ 2 = ‖isotropicEnergyValue 1 U.val‖ ^ 2 +
      ‖isotropicDirichletData (n := n) Ω U‖ ^ 2 := isotropicEnergy_norm_sq 1 U.val
  rw [hnEq]
  nlinarith [sq_nonneg ‖isotropicEnergyValue 1 U.val‖]

instance isotropicDirichletStateRealNormedSpace (Ω : Set D) :
    NormedSpace ℝ (IsotropicDirichletState (n := n) Ω) :=
  (isotropicRealSupported (n := n) Ω).normedSpace

instance isotropicDirichletStateRealInner (Ω : Set D) :
    InnerProductSpace ℝ (IsotropicDirichletState (n := n) Ω) := by
  letI := isotropicScalarEnergyRealInner (n := n) 1
  exact Submodule.innerProductSpace (isotropicRealSupported (n := n) Ω)

/-- The genuine half-order energy pairing as a real bilinear map. -/
def isotropicDirichletFormLinear (Ω : Set D) :
    IsotropicDirichletState (n := n) Ω →ₗ[ℝ] IsotropicDirichletState (n := n) Ω →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun U V ↦ 2 * Real.pi * ⟪isotropicDirichletData (n := n) Ω U,
      isotropicDirichletData (n := n) Ω V⟫)
    (by intro U V W; simp only [map_add, inner_add_left]; ring)
    (by intro c U V; simp only [map_smul, real_inner_smul_left, smul_eq_mul]; ring)
    (by intro U V W; simp only [map_add, inner_add_right]; ring)
    (by intro c U V; simp only [map_smul, real_inner_smul_right, smul_eq_mul]; ring)

/-- The bounded physical square-root-Laplacian form, with the Fourier factor `2π`. -/
def isotropicDirichletForm (Ω : Set D) :
    IsotropicDirichletState (n := n) Ω →L[ℝ] IsotropicDirichletState (n := n) Ω →L[ℝ] ℝ := by
  letI := isotropicDirichletStateRealNormedSpace (n := n) Ω
  exact LinearMap.mkContinuous₂ (E := IsotropicDirichletState (n := n) Ω)
    (F := IsotropicDirichletState (n := n) Ω) (G := ℝ)
    (isotropicDirichletFormLinear (n := n) Ω) (2 * Real.pi) (by
      intro U V
      have hU : ‖isotropicDirichletData (n := n) Ω U‖ ≤ ‖U‖ :=
        PiLp.norm_apply_le _ 1
      have hV : ‖isotropicDirichletData (n := n) Ω V‖ ≤ ‖V‖ :=
        PiLp.norm_apply_le _ 1
      change ‖2 * Real.pi * ⟪isotropicDirichletData Ω U,
        isotropicDirichletData Ω V⟫‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      calc
        _ ≤ 2 * Real.pi * (‖isotropicDirichletData (n := n) Ω U‖ *
            ‖isotropicDirichletData (n := n) Ω V‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by positivity)
        _ ≤ 2 * Real.pi * (‖U‖ * ‖V‖) := by gcongr
        _ = _ := by ring)

/-- The form is the actual weighted Fourier-data pairing. -/
theorem isotropicDirichletForm_apply (Ω : Set D) (U V : IsotropicDirichletState (n := n) Ω) :
    isotropicDirichletForm (n := n) Ω U V =
      2 * Real.pi * ⟪isotropicDirichletData (n := n) Ω U,
        isotropicDirichletData (n := n) Ω V⟫ := rfl

/-- The Riesz representative of the genuine isotropic Dirichlet form. -/
def isotropicDirichletOperator (Ω : Set D) :
    IsotropicDirichletState (n := n) Ω →L[ℝ] IsotropicDirichletState (n := n) Ω :=
  continuousLinearMapOfBilin (𝕜 := ℝ) (E := IsotropicDirichletState (n := n) Ω)
    (isotropicDirichletForm (n := n) Ω)

theorem inner_isotropicDirichletOperator (Ω : Set D) (U V : IsotropicDirichletState (n := n) Ω) :
    ⟪isotropicDirichletOperator (n := n) Ω U, V⟫ = isotropicDirichletForm (n := n) Ω U V :=
  continuousLinearMapOfBilin_apply (𝕜 := ℝ) (E := IsotropicDirichletState (n := n) Ω) _ _ _

/-- The true half-order Dirichlet operator is symmetric and positive. -/
theorem isPositive_isotropicDirichletOperator (Ω : Set D) :
    ContinuousLinearMap.IsPositive (𝕜 := ℝ) (E := IsotropicDirichletState (n := n) Ω)
      (isotropicDirichletOperator (n := n) Ω) := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨?_, ?_⟩
  · intro U V
    change ⟪isotropicDirichletOperator (n := n) Ω U, V⟫ =
      ⟪U, isotropicDirichletOperator (n := n) Ω V⟫
    rw [inner_isotropicDirichletOperator, real_inner_comm,
      inner_isotropicDirichletOperator, isotropicDirichletForm_apply,
      isotropicDirichletForm_apply, real_inner_comm]
  · intro U
    change 0 ≤ ⟪isotropicDirichletOperator (n := n) Ω U, U⟫
    rw [inner_isotropicDirichletOperator, isotropicDirichletForm_apply,
      real_inner_self_eq_norm_sq]
    positivity

/-- Every actual finite-volume domain gives a coercive half-order Dirichlet operator. -/
theorem exists_coercive_isotropicDirichletOperator (hn : 0 < n)
    {Ω : Set D} (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ U : IsotropicDirichletState (n := n) Ω,
      c * ‖U‖ ^ 2 ≤ ⟪isotropicDirichletOperator (n := n) Ω U, U⟫ := by
  obtain ⟨C, hC, hb⟩ := exists_isotropicDirichlet_graph_energy_bound hn hΩ hfin
  refine ⟨(2 * Real.pi) / C, by positivity, fun U ↦ ?_⟩
  rw [inner_isotropicDirichletOperator, isotropicDirichletForm_apply,
    real_inner_self_eq_norm_sq]
  have h := mul_le_mul_of_nonneg_left (hb U) (by positivity : 0 ≤ 2 * Real.pi / C)
  convert h using 1
  field_simp

end PartialBalayage.Linear
