/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceProjectionBalayage
public import PartialBalayage.Linear.IdentityComponent
public import PartialBalayage.Linear.ExtendedLevelSet
public import PartialBalayage.Constants.Linear

/-!
# Actual gradient and Leray projection level-set estimates

Genuine complex-vector partial balayage constructs the capped density, its mass and
active-volume bounds, and agreement of both projections outside the active set.
Removing half the identity gives the exact half-norm energy estimate. The proved
unique cubic parameter gives the table coefficient at every extended-real level.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {n : ℕ}

private theorem projection_coefficient_nnreal (a : ℝ≥0) (ha : a < 1) :
    (((1 / a + (1 / 2 : ℝ≥0) ^ (2 : ℕ) * a /
      (1 - (1 / 2 : ℝ≥0) * a) ^ (2 : ℕ) : ℝ≥0) : ℝ)) =
        projectionCoefficient (a : ℝ) := by
  have haa : (a : ℝ) < 1 := by exact_mod_cast ha
  have hca : (1 / 2 : ℝ≥0) * a ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    change (1 / 2 : ℝ) * (a : ℝ) ≤ 1
    nlinarith [a.coe_nonneg]
  have hne : (1 : ℝ) - 1 / 2 * a ≠ 0 := by nlinarith [a.coe_nonneg]
  have hne' : (2 : ℝ) - a ≠ 0 := by linarith
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_sub hca]
  unfold projectionCoefficient
  field_simp

private theorem projection_levelSet_bound_of_data
    (T S : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin n)) 2 volume)
    (hsplit : T = (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ _ + S)
    (hS : ‖S‖₊ ≤ (1 / 2 : ℝ≥0))
    (f ν : Lp (EuclideanSpace ℂ (Fin n)) 2 volume)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (heq : ∀ᵐ x, x ∉ s → T f x = T ν x)
    {t : ℝ≥0} (ht : 0 < t)
    (hcap : ∀ᵐ x, ‖ν x‖ ≤ projectionParameter * (t : ℝ))
    (hmass : ∫⁻ x, ‖ν x‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ)
    (hs_mass : ENNReal.ofReal (projectionParameter * (t : ℝ)) * volume s ≤
      ∫⁻ x, ‖f x‖ₑ) :
    (t : ℝ≥0∞) * volume {x | (t : ℝ≥0∞) < ‖T f x‖ₑ} ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) * ∫⁻ x, ‖f x‖ₑ := by
  let a : ℝ≥0 := ⟨projectionParameter, projectionParameter_mem.1.le⟩
  have ha : 0 < a := by exact_mod_cast projectionParameter_mem.1
  have ha1 : a < 1 := by exact_mod_cast projectionParameter_mem.2
  have hca : ‖(1 / 2 : ℂ)‖₊ * a < 1 := by
    have hn : ‖(1 / 2 : ℂ)‖₊ = (1 / 2 : ℝ≥0) := by norm_num
    rw [hn]
    apply NNReal.coe_lt_coe.mp
    change (1 / 2 : ℝ) * projectionParameter < 1
    nlinarith [projectionParameter_mem.1, projectionParameter_mem.2]
  have heq' : ∀ᵐ x, x ∉ s → T f x = (1 / 2 : ℂ) • ν x + S ν x := by
    have hv : T ν = (1 / 2 : ℂ) • ν + S ν := by rw [hsplit]; rfl
    filter_upwards [heq, Lp.coeFn_add ((1 / 2 : ℂ) • ν) (S ν),
      Lp.coeFn_smul (1 / 2 : ℂ) ν] with x hx hadd hsmul
    intro hxs
    simp only [Pi.add_apply, Pi.smul_apply] at hadd hsmul
    rw [hx hxs, hv, hadd, hsmul]
  have hT : eLpNorm (S ν) 2 volume ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) *
      eLpNorm ν 2 volume := by
    apply eLpNorm_le_of_Lp_norm_bound
    exact (S.le_opNorm ν).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (norm_nonneg ν))
  have henergy := operator_energy_le_of_cap (Lp.aestronglyMeasurable ν) hcap hT hmass
  have haco : ((a * t : ℝ≥0) : ℝ) = projectionParameter * (t : ℝ) := rfl
  have hcap' : ∀ᵐ x, ‖ν x‖ ≤ ((a * t : ℝ≥0) : ℝ) := by
    simpa only [haco] using hcap
  have hs_mass' : ((a * t : ℝ≥0) : ℝ≥0∞) * volume s ≤ ∫⁻ x, ‖f x‖ₑ := by
    rw [← ENNReal.ofReal_coe_nnreal, haco]
    exact hs_mass
  have henergy' : eLpNorm (S ν) 2 volume ^ (2 : ℕ) ≤
      ((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ) * ((a * t : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ x, ‖f x‖ₑ := by
    rw [← ENNReal.ofReal_coe_nnreal (p := a * t), haco]
    exact henergy
  have hb := levelSet_bound_of_identity_parameter (M := (1 / 2 : ℝ≥0))
    hs heq' ht ha hca hcap' hs_mass' henergy'
  have hn : ‖(1 / 2 : ℂ)‖₊ = (1 / 2 : ℝ≥0) := by norm_num
  rw [hn] at hb
  have hc := projection_coefficient_nnreal a ha1
  have hc' : ((1 / a + (1 / 2 : ℝ≥0) ^ (2 : ℕ) * a /
      (1 - (1 / 2 : ℝ≥0) * a) ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (projectionCoefficient projectionParameter) := by
    change _ = ENNReal.ofReal (projectionCoefficient (a : ℝ))
    rw [← hc]
    exact ENNReal.ofReal_coe_nnreal.symm
  simpa only [hc'] using hb

/-- The actual gradient projection has the exact cubic-root table coefficient. -/
theorem gradientProjection_levelSet_bound (hn : 1 ≤ n)
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : Integrable f volume) (α : ℝ≥0∞) :
    α * volume {x | α < ‖gradientProjectionL2CLM f x‖ₑ} ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) * ∫⁻ x, ‖f x‖ₑ := by
  apply levelSet_bound_all_of_nnreal
  intro t ht
  let a : ℝ≥0 := ⟨projectionParameter, projectionParameter_mem.1.le⟩
  have ha : 0 < a := by exact_mod_cast projectionParameter_mem.1
  obtain ⟨ν, s, hs, hcap, _, hmass, hs_mass, _, heq, _⟩ :=
    exists_complexVector_projection_capped_decomposition (by omega) f hf (a * t)
      (mul_pos ha ht)
  exact projection_levelSet_bound_of_data _ _ gradientProjectionL2CLM_eq_half_add
    opNNNorm_shiftedGradientProjectionL2CLM_le f ν hs heq ht hcap hmass hs_mass

/-- The actual Leray projection has the same exact cubic-root table coefficient. -/
theorem lerayProjection_levelSet_bound (hn : 1 ≤ n)
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : Integrable f volume) (α : ℝ≥0∞) :
    α * volume {x | α < ‖lerayProjectionL2CLM f x‖ₑ} ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) * ∫⁻ x, ‖f x‖ₑ := by
  apply levelSet_bound_all_of_nnreal
  intro t ht
  let a : ℝ≥0 := ⟨projectionParameter, projectionParameter_mem.1.le⟩
  have ha : 0 < a := by exact_mod_cast projectionParameter_mem.1
  obtain ⟨ν, s, hs, hcap, _, hmass, hs_mass, _, _, heq, _⟩ :=
    exists_complexVector_projection_capped_decomposition (by omega) f hf (a * t)
      (mul_pos ha ht)
  exact projection_levelSet_bound_of_data _ _ lerayProjectionL2CLM_eq_half_add
    opNNNorm_shiftedLerayProjectionL2CLM_le f ν hs heq ht hcap hmass hs_mass

end PartialBalayage.Linear
