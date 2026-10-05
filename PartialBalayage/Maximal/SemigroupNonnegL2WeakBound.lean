/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.ScalarSemigroupOffActiveCap
public import PartialBalayage.Maximal.RationalTimeMaximal
public import PartialBalayage.Maximal.CappedMaximalLevelSet

/-!
# Exact semigroup weak bounds for genuine nonnegative integrable `L²` input

The actual positive scalar obstacle controls every fixed positive-time convolution off its
measurable active set. Time continuity passes countably many rational-time bounds to the full
maximal function. Choosing the true density cap as level divided by the exact majorant mass
then proves the genuine level-set estimate, including zero and infinite levels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PartialBalayage.Linear PartialBalayage.Constants
open scoped NNReal ENNReal

namespace PartialBalayage

/-- Almost everywhere input equality gives pointwise equality of heat maximal functions. -/
theorem heatMaximalFunction_congr_ae {d : ℕ}
    {f g : EuclideanSpace ℝ (Fin d) → ℝ} (heq : f =ᵐ[volume] g)
    (x : EuclideanSpace ℝ (Fin d)) : heatMaximalFunction f x = heatMaximalFunction g x := by
  unfold heatMaximalFunction
  apply iSup_congr
  intro t
  apply iSup_congr
  intro _
  apply lintegral_congr_ae
  filter_upwards [heq] with y hy
  rw [hy]

/-- Almost everywhere input equality gives pointwise equality of Poisson maximal functions. -/
theorem poissonMaximalFunction_congr_ae {d : ℕ}
    {f g : EuclideanSpace ℝ (Fin d) → ℝ} (heq : f =ᵐ[volume] g)
    (x : EuclideanSpace ℝ (Fin d)) :
    poissonMaximalFunction f x = poissonMaximalFunction g x := by
  unfold poissonMaximalFunction
  apply iSup_congr
  intro t
  apply iSup_congr
  intro _
  apply lintegral_congr_ae
  filter_upwards [heq] with y hy
  rw [hy]

/-- The genuine heat maximal level-set estimate for nonnegative integrable actual scalar `L²`. -/
theorem heatMaximalFunction_levelSet_bound_of_nonneg_Lp {n : ℕ} {a : ℝ}
    (hroot : IsHeatTangencyParameter (n + 1) a)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ))
    (hf0 : ∀ᵐ x, 0 ≤ f x) (α : ℝ≥0∞) :
    α * volume {x | α < heatMaximalFunction f x} ≤
      ENNReal.ofReal (heatBoundFormula (n + 1) a (rho (n + 1) * a)) * ∫⁻ x, ‖f x‖ₑ := by
  by_cases hα0 : α = 0
  · simp only [hα0, zero_mul, zero_le]
  by_cases hαtop : α = ⊤
  · simp only [hαtop, not_top_lt, ofPred_false, measure_empty, mul_zero,
      zero_le]
  have hαeq : (α.toNNReal : ℝ≥0∞) = α := ENNReal.coe_toNNReal hαtop
  have ht : 0 < α.toNNReal := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    apply hα0
    rw [← hαeq, hzero, ENNReal.coe_zero]
  have hBreal : 0 < heatBoundFormula (n + 1) a (rho (n + 1) * a) :=
    zero_lt_one.trans_le (one_le_heatBoundFormula_of_tangency (by omega) hroot)
  let B : ℝ≥0 := ⟨heatBoundFormula (n + 1) a (rho (n + 1) * a), hBreal.le⟩
  have hB : 0 < B := by exact_mod_cast hBreal
  let κ : ℝ≥0 := α.toNNReal / B
  have hκ : 0 < κ := div_pos ht hB
  obtain ⟨U, hcap, hheat, _⟩ := exists_scalarSemigroup_off_active_caps f hf hf0 κ hκ
  have hκB : (κ : ℝ) * heatBoundFormula (n + 1) a (rho (n + 1) * a) =
      (α.toNNReal : ℝ) := by
    change ((α.toNNReal : ℝ) / (B : ℝ)) * (B : ℝ) = (α.toNNReal : ℝ)
    exact div_mul_cancel₀ _ (by exact_mod_cast hB.ne')
  have hoff := ae_heatMaximalFunction_le_of_nonneg_rational_bounds hf hf0
    (fun x ↦ x ∉ globalBalayageActiveSet U)
    (fun _ ↦ (κ : ℝ) * heatBoundFormula (n + 1) a (rho (n + 1) * a))
    (fun q hq ↦ hheat a hroot q hq)
  have hoff' : ∀ᵐ x, x ∉ globalBalayageActiveSet U →
      heatMaximalFunction f x ≤ (α.toNNReal : ℝ≥0∞) := by
    simpa only [hκB, ENNReal.ofReal_coe_nnreal] using hoff
  have hcap' : ((α.toNNReal / B : ℝ≥0) : ℝ≥0∞) *
      volume (globalBalayageActiveSet U) ≤ ∫⁻ x, ‖f x‖ₑ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hcap
  have h := maximal_levelSet_bound_of_cap_quotient hB hoff' hcap'
  have hBcoe : (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) :=
    ENNReal.ofReal_coe_nnreal.symm
  rw [hBcoe, hαeq] at h
  exact h

/-- The genuine Poisson maximal level-set estimate for nonnegative integrable actual scalar `L²`. -/
theorem poissonMaximalFunction_levelSet_bound_of_nonneg_Lp {n : ℕ} {a : ℝ}
    (hroot : IsPoissonTangencyParameter (n + 1) a)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ))
    (hf0 : ∀ᵐ x, 0 ≤ f x) (α : ℝ≥0∞) :
    α * volume {x | α < poissonMaximalFunction f x} ≤
      ENNReal.ofReal (poissonBoundFormula (n + 1) a (rho (n + 1) * a)) * ∫⁻ x, ‖f x‖ₑ := by
  by_cases hα0 : α = 0
  · simp only [hα0, zero_mul, zero_le]
  by_cases hαtop : α = ⊤
  · simp only [hαtop, not_top_lt, ofPred_false, measure_empty, mul_zero,
      zero_le]
  have hαeq : (α.toNNReal : ℝ≥0∞) = α := ENNReal.coe_toNNReal hαtop
  have ht : 0 < α.toNNReal := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    apply hα0
    rw [← hαeq, hzero, ENNReal.coe_zero]
  have hBreal : 0 < poissonBoundFormula (n + 1) a (rho (n + 1) * a) :=
    zero_lt_one.trans_le (one_le_poissonBoundFormula_of_tangency (by omega) hroot)
  let B : ℝ≥0 := ⟨poissonBoundFormula (n + 1) a (rho (n + 1) * a), hBreal.le⟩
  have hB : 0 < B := by exact_mod_cast hBreal
  let κ : ℝ≥0 := α.toNNReal / B
  have hκ : 0 < κ := div_pos ht hB
  obtain ⟨U, hcap, _, hpoisson⟩ := exists_scalarSemigroup_off_active_caps f hf hf0 κ hκ
  have hκB : (κ : ℝ) * poissonBoundFormula (n + 1) a (rho (n + 1) * a) =
      (α.toNNReal : ℝ) := by
    change ((α.toNNReal : ℝ) / (B : ℝ)) * (B : ℝ) = (α.toNNReal : ℝ)
    exact div_mul_cancel₀ _ (by exact_mod_cast hB.ne')
  have hoff := ae_poissonMaximalFunction_le_of_nonneg_rational_bounds hf hf0
    (fun x ↦ x ∉ globalBalayageActiveSet U)
    (fun _ ↦ (κ : ℝ) * poissonBoundFormula (n + 1) a (rho (n + 1) * a))
    (fun q hq ↦ hpoisson a hroot q hq)
  have hoff' : ∀ᵐ x, x ∉ globalBalayageActiveSet U →
      poissonMaximalFunction f x ≤ (α.toNNReal : ℝ≥0∞) := by
    simpa only [hκB, ENNReal.ofReal_coe_nnreal] using hoff
  have hcap' : ((α.toNNReal / B : ℝ≥0) : ℝ≥0∞) *
      volume (globalBalayageActiveSet U) ≤ ∫⁻ x, ‖f x‖ₑ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hcap
  have h := maximal_levelSet_bound_of_cap_quotient hB hoff' hcap'
  have hBcoe : (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) :=
    ENNReal.ofReal_coe_nnreal.symm
  rw [hBcoe, hαeq] at h
  exact h

/-- The exact heat estimate for any genuine nonnegative function in `L¹ ∩ L²`. -/
theorem heatMaximalFunction_levelSet_bound_of_nonneg_memLp {n : ℕ} {a : ℝ}
    (hroot : IsHeatTangencyParameter (n + 1) a)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) (hf0 : ∀ᵐ x, 0 ≤ f x) (α : ℝ≥0∞) :
    α * volume {x | α < heatMaximalFunction f x} ≤
      ENNReal.ofReal (heatBoundFormula (n + 1) a (rho (n + 1) * a)) * ∫⁻ x, ‖f x‖ₑ := by
  let F := hf2.toLp f
  have heq : (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hF : Integrable (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := hf.congr heq.symm
  have hF0 : ∀ᵐ x, 0 ≤ F x := by
    filter_upwards [hf0, heq] with x hx hFx
    rwa [hFx]
  have h := heatMaximalFunction_levelSet_bound_of_nonneg_Lp hroot F hF hF0 α
  have hset : {x | α < heatMaximalFunction F x} = {x | α < heatMaximalFunction f x} := by
    ext x
    change (α < heatMaximalFunction F x) ↔ (α < heatMaximalFunction f x)
    rw [heatMaximalFunction_congr_ae heq x]
  have hmass : (∫⁻ x, ‖F x‖ₑ) = ∫⁻ x, ‖f x‖ₑ := by
    apply lintegral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  rw [hset, hmass] at h
  exact h

/-- The exact Poisson estimate for any genuine nonnegative function in `L¹ ∩ L²`. -/
theorem poissonMaximalFunction_levelSet_bound_of_nonneg_memLp {n : ℕ} {a : ℝ}
    (hroot : IsPoissonTangencyParameter (n + 1) a)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) (hf0 : ∀ᵐ x, 0 ≤ f x) (α : ℝ≥0∞) :
    α * volume {x | α < poissonMaximalFunction f x} ≤
      ENNReal.ofReal (poissonBoundFormula (n + 1) a (rho (n + 1) * a)) * ∫⁻ x, ‖f x‖ₑ := by
  let F := hf2.toLp f
  have heq : (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hF : Integrable (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := hf.congr heq.symm
  have hF0 : ∀ᵐ x, 0 ≤ F x := by
    filter_upwards [hf0, heq] with x hx hFx
    rwa [hFx]
  have h := poissonMaximalFunction_levelSet_bound_of_nonneg_Lp hroot F hF hF0 α
  have hset : {x | α < poissonMaximalFunction F x} =
      {x | α < poissonMaximalFunction f x} := by
    ext x
    change (α < poissonMaximalFunction F x) ↔ (α < poissonMaximalFunction f x)
    rw [poissonMaximalFunction_congr_ae heq x]
  have hmass : (∫⁻ x, ‖F x‖ₑ) = ∫⁻ x, ‖f x‖ₑ := by
    apply lintegral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  rw [hset, hmass] at h
  exact h

end PartialBalayage
