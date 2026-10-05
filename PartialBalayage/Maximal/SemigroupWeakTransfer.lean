/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.KernelWeakBoundTransfer
public import PartialBalayage.Maximal.SemigroupTimeContinuity

/-!
# Genuine L¹ extension of heat and Poisson weak bounds

The original positive kernels meet the hypotheses of monotone kernel transfer.
Thus an exact coefficient proved on actual L¹ and L² inputs bounds each original
all-positive-time maximal operator on every integrable real input.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace PartialBalayage

variable {n : ℕ}

/-- The genuine heat kernel weak bound on L¹ and L² extends to all L¹ inputs. -/
theorem isHeatWeakTypeBound_of_L1_L2 (C : ℝ≥0∞)
    (hb : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → MemLp f 2 volume →
      ∀ α : ℝ≥0∞, α * volume {x | α < heatMaximalFunction f x} ≤
        C * ∫⁻ y, ‖f y‖ₑ) :
    IsHeatWeakTypeBound n C := by
  let K : {t : ℝ // 0 < t} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun t x y ↦ ENNReal.ofReal (heatKernel n t (x - y))
  have hK : ∀ t x, AEMeasurable (K t x) volume := by
    intro t x
    exact (ENNReal.continuous_ofReal.comp
      ((continuous_heatKernel_space n t).comp
        (continuous_const.sub continuous_id))).measurable.aemeasurable
  have h := kernel_maximal_weak_bound_of_L1_L2 K hK C
    (fun f hf hf2 α ↦ by simpa only [K, iSup_subtype, heatMaximalFunction] using hb f hf hf2 α)
  simpa only [K, iSup_subtype, IsHeatWeakTypeBound, heatMaximalFunction] using h

/-- The genuine Poisson kernel weak bound on L¹ and L² extends to all L¹ inputs. -/
theorem isPoissonWeakTypeBound_of_L1_L2 (C : ℝ≥0∞)
    (hb : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → MemLp f 2 volume →
      ∀ α : ℝ≥0∞, α * volume {x | α < poissonMaximalFunction f x} ≤
        C * ∫⁻ y, ‖f y‖ₑ) :
    IsPoissonWeakTypeBound n C := by
  let K : {t : ℝ // 0 < t} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun t x y ↦ ENNReal.ofReal (poissonKernel n t (x - y))
  have hK : ∀ t x, AEMeasurable (K t x) volume := by
    intro t x
    exact (ENNReal.continuous_ofReal.comp
      ((continuous_poissonKernel_space n t.property).comp
        (continuous_const.sub continuous_id))).measurable.aemeasurable
  have h := kernel_maximal_weak_bound_of_L1_L2 K hK C
    (fun f hf hf2 α ↦ by
      simpa only [K, iSup_subtype, poissonMaximalFunction] using hb f hf hf2 α)
  simpa only [K, iSup_subtype, IsPoissonWeakTypeBound, poissonMaximalFunction] using h

/-- It suffices to prove the true heat estimate for nonnegative L¹ and L² inputs. -/
theorem isHeatWeakTypeBound_of_nonneg_L1_L2 (C : ℝ≥0∞)
    (hb : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → MemLp f 2 volume →
      (∀ᵐ x, 0 ≤ f x) → ∀ α : ℝ≥0∞, α * volume {x | α < heatMaximalFunction f x} ≤
        C * ∫⁻ y, ‖f y‖ₑ) :
    IsHeatWeakTypeBound n C := by
  apply isHeatWeakTypeBound_of_L1_L2 C
  intro f hf hf2 α
  simpa only [heatMaximalFunction, enorm_norm] using
    hb (fun y ↦ ‖f y‖) hf.norm hf2.norm
      (Eventually.of_forall fun y ↦ norm_nonneg (f y)) α

/-- It suffices to prove the true Poisson estimate for nonnegative L¹ and L² inputs. -/
theorem isPoissonWeakTypeBound_of_nonneg_L1_L2 (C : ℝ≥0∞)
    (hb : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → MemLp f 2 volume →
      (∀ᵐ x, 0 ≤ f x) → ∀ α : ℝ≥0∞, α * volume {x | α < poissonMaximalFunction f x} ≤
        C * ∫⁻ y, ‖f y‖ₑ) :
    IsPoissonWeakTypeBound n C := by
  apply isPoissonWeakTypeBound_of_L1_L2 C
  intro f hf hf2 α
  simpa only [poissonMaximalFunction, enorm_norm] using
    hb (fun y ↦ ‖f y‖) hf.norm hf2.norm
      (Eventually.of_forall fun y ↦ norm_nonneg (f y)) α

end PartialBalayage
