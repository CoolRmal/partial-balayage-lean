/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexPoissonDirichletEnergyMass
public import PartialBalayage.Linear.WeakDirichletEnergy

/-!
# Genuine weak lower semicontinuity of bounded Poisson energy and full mass

The actual bounded Poisson difference quotient defines a continuous nonnegative quadratic
form on ordinary complex `L²`. Its convexity gives weak lower semicontinuity. Adding the actual
full norm integral preserves it, so the same finite obstacle balances control an ordinary
weak limit before any half-order regularity of that limit has been established.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace PartialBalayage.Linear.ComplexPoisson

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure D)

/-- The actual complex bounded Poisson quotient over real scalars as a continuous linear map. -/
def poissonRealQuotientL2CLM {t : ℝ} (ht : 0 < t) : L² →L[ℝ] L² :=
  t⁻¹ • (ContinuousLinearMap.id ℝ _ - poissonConvolutionL2CLM ht)

/-- The actual real quadratic defect, with no assumed Fourier-energy finiteness. -/
def poissonRealQuadraticDefect {t : ℝ} (ht : 0 < t) (f : L²) : ℝ :=
  ⟪f, poissonRealQuotientL2CLM ht f⟫

/-- Actual real scalar restriction gives exactly the same spatial Poisson defect. -/
theorem poissonRealQuadraticDefect_eq {t : ℝ} (ht : 0 < t) (f : L²) :
    poissonRealQuadraticDefect ht f =
      poissonQuadraticDefect ht f := by
  rw [poissonQuadraticDefect, ← real_inner_complexLp, poissonQuotientL2_eq_real_smul]
  rfl

theorem poissonRealQuadraticDefect_nonneg {t : ℝ} (ht : 0 < t) (f : L²) :
    0 ≤ poissonRealQuadraticDefect ht f := by
  rw [poissonRealQuadraticDefect_eq]
  exact poissonQuadraticDefect_nonneg ht _

private theorem poissonRealQuadraticDefect_jensen {t : ℝ} (ht : 0 < t)
    (u v : L²) (a b : ℝ) (hab : a + b = 1) :
    poissonRealQuadraticDefect ht (a • u + b • v) =
      a * poissonRealQuadraticDefect ht u + b * poissonRealQuadraticDefect ht v -
        a * b * poissonRealQuadraticDefect ht (u - v) := by
  simp only [poissonRealQuadraticDefect, map_add, map_smul, map_sub,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right]
  linear_combination
    (a * ⟪u, poissonRealQuotientL2CLM ht u⟫ +
      b * ⟪v, poissonRealQuotientL2CLM ht v⟫) * hab

/-- Positivity of the actual quotient gives convexity of its true quadratic energy. -/
theorem convexOn_poissonRealQuadraticDefect {t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ univ (poissonRealQuadraticDefect (n := n) ht) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  change poissonRealQuadraticDefect ht (a • u + b • v) ≤
    a * poissonRealQuadraticDefect ht u + b * poissonRealQuadraticDefect ht v
  rw [poissonRealQuadraticDefect_jensen ht u v a b hab]
  exact sub_le_self _
    (mul_nonneg (mul_nonneg ha hb) (poissonRealQuadraticDefect_nonneg ht (u - v)))

theorem continuous_poissonRealQuadraticDefect {t : ℝ} (ht : 0 < t) :
    Continuous (poissonRealQuadraticDefect (n := n) ht) :=
  continuous_id.inner (poissonRealQuotientL2CLM ht).continuous

/-- The genuine bounded quadratic defect is lower semicontinuous under weak `L²` convergence. -/
theorem lowerSemicontinuous_poissonRealQuadraticDefect_weak {t : ℝ} (ht : 0 < t) :
    LowerSemicontinuous (poissonRealQuadraticDefect (n := n) ht ∘
      (toWeakSpace ℝ L²).symm) :=
  (convexOn_poissonRealQuadraticDefect ht).lowerSemicontinuous_comp_toWeakSpace_symm
    (continuous_poissonRealQuadraticDefect ht).lowerSemicontinuous

/-- Actual bounded Poisson energy plus the genuine extended cap-weighted full norm mass. -/
def poissonDefectEnergyMass {t : ℝ} (ht : 0 < t) (κ : ℝ) (f : L²) : ℝ≥0∞ :=
  ENNReal.ofReal (poissonRealQuadraticDefect ht f) +
    ENNReal.ofReal κ * ∫⁻ x, ‖f x‖ₑ

/-- The whole genuine extended functional is lower semicontinuous in the ordinary weak space. -/
theorem lowerSemicontinuous_poissonDefectEnergyMass_weak {t : ℝ} (ht : 0 < t) (κ : ℝ) :
    LowerSemicontinuous (poissonDefectEnergyMass (n := n) ht κ ∘
      (toWeakSpace ℝ L²).symm) := by
  apply LowerSemicontinuous.add
  · exact ENNReal.continuous_ofReal.comp_lowerSemicontinuous
      (lowerSemicontinuous_poissonRealQuadraticDefect_weak ht)
      (fun _ _ h ↦ ENNReal.ofReal_le_ofReal h)
  · exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      lowerSemicontinuous_lintegral_norm_weak (fun _ _ h ↦ mul_le_mul_right h _)

/-- Genuine integrable values identify the extended expression with ordinary energy and mass. -/
theorem poissonDefectEnergyMass_of_integrable {t κ : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ)
    (f : L²) (hf : Integrable (f : D → ℂ)) :
    poissonDefectEnergyMass ht κ f = ENNReal.ofReal (poissonRealQuadraticDefect ht f +
      κ * ∫ x, ‖f x‖) := by
  rw [poissonDefectEnergyMass, ← ofReal_integral_norm_eq_lintegral_enorm hf,
    ← ENNReal.ofReal_mul hκ, ENNReal.ofReal_add (poissonRealQuadraticDefect_nonneg ht f)
      (mul_nonneg hκ (integral_nonneg (fun _ ↦ norm_nonneg _)))]

/-- The exact same actual finite balances pass to an ordinary weak limit at fixed height. -/
theorem poissonDefectEnergyMass_le_of_weak_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {t : ℝ} (ht : 0 < t) (κ : ℝ) {u : ι → L²} {limit : L²}
    (hut : Tendsto (fun k ↦ toWeakSpace ℝ L² (u k)) l (𝓝 (toWeakSpace ℝ L² limit)))
    (ℓ : L² →L[ℝ] ℝ)
    (hbound : ∀ᶠ k in l, poissonDefectEnergyMass ht κ (u k) ≤ ENNReal.ofReal (ℓ (u k))) :
    poissonDefectEnergyMass ht κ limit ≤ ENNReal.ofReal (ℓ limit) := by
  have hp : Tendsto (fun k ↦ ENNReal.ofReal (ℓ (u k))) l
      (𝓝 (ENNReal.ofReal (ℓ limit))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp
      ((ℓ.continuous_comp_toWeakSpace_symm.tendsto _).comp hut)
  by_contra hn
  obtain ⟨r, hpr, hr⟩ := exists_between (lt_of_not_ge hn)
  have hlo : ∀ᶠ k in l, r < poissonDefectEnergyMass ht κ (u k) :=
    hut.eventually ((lowerSemicontinuous_poissonDefectEnergyMass_weak ht κ)
      (toWeakSpace ℝ L² limit) r hr)
  have hhi : ∀ᶠ k in l, ENNReal.ofReal (ℓ (u k)) < r :=
    hp.eventually (eventually_lt_nhds hpr)
  obtain ⟨k, hklo, hkhi, hkbound⟩ := (hlo.and (hhi.and hbound)).exists
  exact (not_lt_of_ge (hklo.le.trans hkbound)) hkhi

/-- A positive cap weight and a genuine fixed-height bound force full integrability. -/
theorem integrable_poissonState_of_defectEnergyMass_le {t κ b : ℝ} (ht : 0 < t)
    (hκ : 0 < κ) (f : L²) (hbound : poissonDefectEnergyMass ht κ f ≤ ENNReal.ofReal b) :
    Integrable (f : D → ℂ) := by
  have hc : ENNReal.ofReal κ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hκ
  have hm : ENNReal.ofReal κ * (∫⁻ x, ‖f x‖ₑ) ≤ ENNReal.ofReal b :=
    (le_add_of_nonneg_left zero_le).trans hbound
  have hfin : (∫⁻ x, ‖f x‖ₑ) ≠ ⊤ := by
    intro htop
    have hmul := ENNReal.mul_eq_top.mpr (Or.inl ⟨hc, htop⟩)
    exact ENNReal.ofReal_ne_top (top_unique (hmul ▸ hm))
  exact ⟨Lp.aestronglyMeasurable _, hasFiniteIntegral_iff_enorm.mpr hfin.lt_top⟩

end PartialBalayage.Linear.ComplexPoisson
