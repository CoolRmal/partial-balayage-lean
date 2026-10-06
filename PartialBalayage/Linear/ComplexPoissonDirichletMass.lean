/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonDirichletOperators
public import PartialBalayage.Linear.PoissonL1
public import PartialBalayage.Linear.KatoAveraging
public import PartialBalayage.Linear.ZeroExtensionMass

/-!
# Actual finite signed Poisson-obstacle mass contraction

The bounded difference quotient admits its genuine measurable norm-supporting direction
as a test. Choose the state's sign on its active set and the density's sign elsewhere.
The actual positive averaging Kato inequality and full first-moment contraction then
control the density's entire mass, including points where the state vanishes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)

/-- The true Kato direction supports the state norm and the inactive density norm. -/
def signedPoissonKatoDirection (u ν : ℂ) : ℂ :=
  if u = 0 then capSupportVector 1 ν else capSupportVector 1 u

theorem norm_signedPoissonKatoDirection_le (u ν : ℂ) :
    ‖signedPoissonKatoDirection u ν‖ ≤ 1 := by
  unfold signedPoissonKatoDirection
  split_ifs <;> exact norm_capSupportVector_le zero_le_one _

/-- This actual direction supports the norm of the state everywhere. -/
theorem inner_signedPoissonKatoDirection_state (u ν : ℂ) :
    ⟪signedPoissonKatoDirection u ν, u⟫ = ‖u‖ := by
  unfold signedPoissonKatoDirection
  split_ifs with hu
  · simp only [hu, inner_zero_right, norm_zero]
  · rw [real_inner_comm]
    simpa only [one_mul] using inner_capSupportVector (1 : ℝ) u

/-- Actual cap alignment makes the same direction support the entire density norm. -/
theorem inner_signedPoissonKatoDirection_density {u ν : ℂ} {κ : ℝ}
    (ha : u ≠ 0 → ν = (κ / ‖u‖) • u) (hs : u ≠ 0 → ‖ν‖ = κ) :
    ⟪signedPoissonKatoDirection u ν, ν⟫ = ‖ν‖ := by
  unfold signedPoissonKatoDirection
  split_ifs with hu
  · rw [real_inner_comm]
    simpa only [one_mul] using inner_capSupportVector (1 : ℝ) ν
  · calc
      ⟪capSupportVector 1 u, ν⟫ = ⟪capSupportVector 1 u, (κ / ‖u‖) • u⟫ :=
        congrArg (inner ℝ (capSupportVector 1 u)) (ha hu)
      _ = κ := by
        rw [real_inner_smul_right, real_inner_comm, inner_capSupportVector, one_mul,
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu)]
      _ = ‖ν‖ := (hs hu).symm

/-- The actual zero extension agrees with its restricted class on the domain. -/
theorem zeroExtendL2_ae_restrict_value {Ω : Set D} (hΩ : MeasurableSet Ω)
    (u : Lp ℂ 2 (volume.restrict Ω)) :
    zeroExtendL2 hΩ u =ᵐ[volume.restrict Ω] u := by
  filter_upwards [ae_restrict_of_ae (zeroExtendL2_ae hΩ u), ae_restrict_mem hΩ]
    with x hx hxo
  rw [hx, indicator_of_mem hxo]

/-- The finite-domain Poisson average has its actual global averaging representative. -/
theorem poissonDirichletAverage_ae {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (u : Lp ℂ 2 (volume.restrict Ω)) :
    poissonDirichletAverage hΩ ht u =ᵐ[volume.restrict Ω]
      poissonConvolution t (zeroExtendL2 hΩ u) :=
  (restrictL2CLM_ae Ω _).trans (ae_restrict_of_ae (poissonConvolutionL2_ae ht _))

/-- The actual bounded operator equation has its ordinary complex spatial form. -/
theorem poissonDirichletOperator_ae {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (ε : ℝ) (u : Lp ℂ 2 (volume.restrict Ω)) :
    poissonDirichletOperator hΩ ht ε u =ᵐ[volume.restrict Ω] fun x ↦
      ε • u x + t⁻¹ • (u x - poissonConvolution t (zeroExtendL2 hΩ u) x) := by
  filter_upwards [Lp.coeFn_add (ε • u) (t⁻¹ • (u - poissonDirichletAverage hΩ ht u)),
    Lp.coeFn_smul ε u, Lp.coeFn_smul t⁻¹ (u - poissonDirichletAverage hΩ ht u),
    Lp.coeFn_sub u (poissonDirichletAverage hΩ ht u), poissonDirichletAverage_ae hΩ ht u]
      with x hadd he ht' hd hP
  change (ε • u + t⁻¹ • (u - poissonDirichletAverage hΩ ht u)) x = _
  simp only [hadd, Pi.add_apply, he, ht', Pi.smul_apply, hd, Pi.sub_apply, hP]

/-- The norm of a complex actual `L²` value is itself a genuine real `L²` class. -/
def poissonRealNormL2 (u : L²) : Lp ℝ 2 (volume : Measure D) :=
  (Lp.memLp u).norm.toLp (fun x ↦ ‖u x‖)

theorem poissonRealNormL2_ae (u : L²) :
    poissonRealNormL2 u =ᵐ[volume] fun x ↦ ‖u x‖ := (Lp.memLp u).norm.coeFn_toLp

/-- The norm average in the finite-domain Kato inequality is an actual `L²` class. -/
def poissonDirichletNormAverage {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (u : Lp ℂ 2 (volume.restrict Ω)) :
    Lp ℝ 2 (volume.restrict Ω) :=
  restrictL2CLM Ω (poissonConvolutionL2 ht (poissonRealNormL2 (zeroExtendL2 hΩ u)))

theorem poissonDirichletNormAverage_ae {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (u : Lp ℂ 2 (volume.restrict Ω)) :
    poissonDirichletNormAverage hΩ ht u =ᵐ[volume.restrict Ω] fun x ↦
      ∫ y, ‖zeroExtendL2 hΩ u (x - y)‖ ∂PartialBalayage.poissonKernelMeasure n t := by
  have hconv := poissonConvolution_congr t (poissonRealNormL2_ae (zeroExtendL2 hΩ u))
  exact (restrictL2CLM_ae Ω _).trans
    (ae_restrict_of_ae ((poissonConvolutionL2_ae ht _).trans
      (Filter.EventuallyEq.of_eq hconv)))

/-- Actual averaging cannot increase the first moment of a zero-exterior state. -/
theorem integral_poissonDirichletNormAverage_le {Ω : Set D} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {t : ℝ} (ht : 0 < t)
    (u : Lp ℂ 2 (volume.restrict Ω)) :
    (∫ x, poissonDirichletNormAverage hΩ ht u x ∂volume.restrict Ω) ≤
      ∫ x, ‖u x‖ ∂volume.restrict Ω := by
  have hi := integrable_zeroExtendL2 hΩ u ((Lp.memLp u).integrable one_le_two)
  have hq : Integrable (poissonRealNormL2 (zeroExtendL2 hΩ u) : D → ℝ) :=
    hi.norm.congr (poissonRealNormL2_ae _).symm
  have hP := integrable_poissonConvolutionL2_of_integrable ht _ hq
  calc
    _ ≤ ∫ x, ‖poissonDirichletNormAverage hΩ ht u x‖ ∂volume.restrict Ω :=
      integral_mono ((Lp.memLp _).integrable one_le_two)
        (((Lp.memLp _).integrable one_le_two).norm) (fun x ↦ le_abs_self _)
    _ ≤ ∫ x, ‖poissonConvolutionL2 ht (poissonRealNormL2 (zeroExtendL2 hΩ u)) x‖ :=
      integral_norm_restrictL2CLM_le Ω _ hP
    _ ≤ ∫ x, ‖poissonRealNormL2 (zeroExtendL2 hΩ u) x‖ :=
      integral_norm_poissonConvolutionL2_le ht _ hq
    _ = ∫ x, ‖zeroExtendL2 hΩ u x‖ := by
      apply integral_congr_ae
      filter_upwards [poissonRealNormL2_ae (zeroExtendL2 hΩ u)] with x hx
      rw [hx, norm_norm]
    _ = _ := integral_norm_zeroExtendL2 hΩ u

/-- The actual finite signed obstacle gives the full pointwise Kato mass inequality. -/
theorem poissonDirichlet_kato_mass_ae {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t ε κ : ℝ} (ht : 0 < t) (f ν u : Lp ℂ 2 (volume.restrict Ω))
    (heq : poissonDirichletOperator hΩ ht ε u = f - ν)
    (ha : ∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ν x = (κ / ‖u x‖) • u x)
    (hs : ∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ‖ν x‖ = κ) :
    ∀ᵐ x ∂volume.restrict Ω, ε * ‖u x‖ + ‖ν x‖ ≤ ‖f x‖ -
      t⁻¹ * (‖u x‖ - poissonDirichletNormAverage hΩ ht u x) := by
  have hep : (poissonDirichletOperator hΩ ht ε u : D → ℂ) =ᵐ[volume.restrict Ω]
      (f - ν : Lp ℂ 2 (volume.restrict Ω)) :=
    Filter.EventuallyEq.of_eq
      (congrArg (fun z : Lp ℂ 2 (volume.restrict Ω) ↦ (z : D → ℂ)) heq)
  filter_upwards [ha, hs, hep, Lp.coeFn_sub f ν, poissonDirichletOperator_ae hΩ ht ε u,
    zeroExtendL2_ae_restrict_value hΩ u, poissonDirichletNormAverage_ae hΩ ht u,
    ae_restrict_of_ae (ae_integrable_poisson_translates ht (zeroExtendL2 hΩ u))]
      with x ha hs hep hsub hOp hExt hAvg hi
  let w := signedPoissonKatoDirection (u x) (ν x)
  have hk := kato_averaging (u := zeroExtendL2 hΩ u x) (w := w) hi
    (norm_signedPoissonKatoDirection_le (u x) (ν x))
    (by rw [hExt]; exact inner_signedPoissonKatoDirection_state _ _)
  rw [← hAvg] at hk
  have hwu := inner_signedPoissonKatoDirection_state (u x) (ν x)
  have hwν := inner_signedPoissonKatoDirection_density ha hs
  have hwf : ⟪w, f x⟫ ≤ ‖f x‖ := by
    exact (real_inner_le_norm w (f x)).trans (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (norm_signedPoissonKatoDirection_le (u x) (ν x)) (norm_nonneg (f x))))
  rw [hExt] at hk
  change ‖u x‖ - poissonDirichletNormAverage hΩ ht u x ≤
    ⟪w, u x - poissonConvolution t (zeroExtendL2 hΩ u) x⟫ at hk
  have hmain : ε • u x + t⁻¹ •
      (u x - poissonConvolution t (zeroExtendL2 hΩ u) x) = f x - ν x := by
    rw [← hOp, hep, hsub, Pi.sub_apply]
  have hm : ε * ‖u x‖ + t⁻¹ *
      ⟪w, u x - poissonConvolution t (zeroExtendL2 hΩ u) x⟫ = ⟪w, f x⟫ - ‖ν x‖ := by
    calc
      _ = ⟪w, ε • u x + t⁻¹ •
          (u x - poissonConvolution t (zeroExtendL2 hΩ u) x)⟫ := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hwu]
      _ = ⟪w, f x - ν x⟫ := congrArg (inner ℝ w) hmain
      _ = _ := by rw [inner_sub_right, hwν]
  have hp := mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr ht.le)
  nlinarith only [hm, hp, hwf]

/-- The finite obstacle contracts the entire density mass, including its inactive set. -/
theorem integral_norm_poissonDirichlet_density_le {Ω : Set D} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {t ε κ : ℝ} (ht : 0 < t) (hε : 0 ≤ ε)
    (f ν u : Lp ℂ 2 (volume.restrict Ω))
    (heq : poissonDirichletOperator hΩ ht ε u = f - ν)
    (ha : ∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ν x = (κ / ‖u x‖) • u x)
    (hs : ∀ᵐ x ∂volume.restrict Ω, u x ≠ 0 → ‖ν x‖ = κ) :
    (∫ x, ‖ν x‖ ∂volume.restrict Ω) ≤ ∫ x, ‖f x‖ ∂volume.restrict Ω := by
  have hu := ((Lp.memLp u).integrable one_le_two).norm
  have hν := ((Lp.memLp ν).integrable one_le_two).norm
  have hf := ((Lp.memLp f).integrable one_le_two).norm
  have hAvg := (Lp.memLp (poissonDirichletNormAverage hΩ ht u)).integrable one_le_two
  have hDiff : Integrable (fun x ↦ ‖u x‖ - poissonDirichletNormAverage hΩ ht u x)
      (volume.restrict Ω) := hu.sub hAvg
  have h := integral_mono_ae (hu.const_mul ε |>.add hν)
    (hf.sub (hu.sub hAvg |>.const_mul t⁻¹)) (poissonDirichlet_kato_mass_ae hΩ ht f ν u heq ha hs)
  change (∫ x, ε * ‖u x‖ + ‖ν x‖ ∂volume.restrict Ω) ≤
    ∫ x, ‖f x‖ - t⁻¹ * (‖u x‖ - poissonDirichletNormAverage hΩ ht u x)
      ∂volume.restrict Ω at h
  rw [integral_add (hu.const_mul ε) hν, integral_const_mul,
    integral_sub hf (hDiff.const_mul t⁻¹), integral_const_mul,
    integral_sub hu hAvg] at h
  have hm := integral_poissonDirichletNormAverage_le hΩ ht u
  have hp : 0 ≤ t⁻¹ * ((∫ x, ‖u x‖ ∂volume.restrict Ω) -
      ∫ x, poissonDirichletNormAverage hΩ ht u x ∂volume.restrict Ω) :=
    mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr hm)
  have hu0 : 0 ≤ ∫ x, ‖u x‖ ∂volume.restrict Ω :=
    integral_nonneg (fun x ↦ norm_nonneg (u x))
  nlinarith [mul_nonneg hε hu0]

end PartialBalayage.Linear.ComplexPoisson
