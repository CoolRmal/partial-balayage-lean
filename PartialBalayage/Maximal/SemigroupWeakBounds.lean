/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupNonnegL2WeakBound
public import PartialBalayage.Maximal.SemigroupWeakTransfer
public import PartialBalayage.Maximal.SemigroupParameters
public import PartialBalayage.Maximal.PlanarBoundFormula
public import PartialBalayage.Maximal.OneDimensionalBoundFormula

/-!
# Unconditional exact heat and Poisson maximal bounds

The genuine positive whole-space obstacle and the exact normalized majorant masses
prove the actual L¹ and L² estimates. Monotone kernel transfer proves the same sharp
coefficients for every integrable real input and every extended-real level. The unique
parameters are selected from the proved exact tangency equations in the article's intervals.
-/

@[expose] public section

open MeasureTheory Set
open PartialBalayage.Constants
open scoped ENNReal

namespace PartialBalayage

/-- The exact heat majorant formula bounds the original maximal operator on every L¹ input. -/
theorem isHeatWeakTypeBound_formula {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsHeatTangencyParameter n a) :
    IsHeatWeakTypeBound n (ENNReal.ofReal (heatBoundFormula n a (rho n * a))) := by
  cases n with
  | zero => omega
  | succ k =>
    apply isHeatWeakTypeBound_of_nonneg_L1_L2
    intro f hf hf2 hf0 α
    exact heatMaximalFunction_levelSet_bound_of_nonneg_memLp hroot f hf hf2 hf0 α

/-- The exact Poisson formula bounds the original maximal operator on every L¹ input. -/
theorem isPoissonWeakTypeBound_formula {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsPoissonTangencyParameter n a) :
    IsPoissonWeakTypeBound n (ENNReal.ofReal (poissonBoundFormula n a (rho n * a))) := by
  cases n with
  | zero => omega
  | succ k =>
    apply isPoissonWeakTypeBound_of_nonneg_L1_L2
    intro f hf hf2 hf0 α
    exact poissonMaximalFunction_levelSet_bound_of_nonneg_memLp hroot f hf hf2 hf0 α

namespace Maximal

/-- The table's exact heat bound in every positive dimension, for all integrable inputs. -/
theorem heat_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    heatWeakTypeConstant n ≤ ENNReal.ofReal
      (heatBoundFormula n (heatTangencyParameter n) (rho n * heatTangencyParameter n)) := by
  exact sInf_le (isHeatWeakTypeBound_formula hn (isHeatTangencyParameter_selected n hn))

/-- The table's exact Poisson bound in every positive dimension, for all integrable inputs. -/
theorem poisson_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    poissonWeakTypeConstant n ≤ ENNReal.ofReal
      (poissonBoundFormula n (poissonTangencyParameter n)
        (rho n * poissonTangencyParameter n)) := by
  exact sInf_le (isPoissonWeakTypeBound_formula hn (isPoissonTangencyParameter_selected n hn))

/-- The planar heat row's exact exponential expression, without a truncated decimal. -/
theorem heat_weakTypeConstant_two_le_exact :
    heatWeakTypeConstant 2 ≤ ENNReal.ofReal
      ((1 + (Real.exp 1 - 1) * heatTangencyParameter 2) *
        Real.exp (-heatTangencyParameter 2)) := by
  have heq := (isHeatTangencyParameter_selected 2 (by norm_num)).2
  norm_num only [rho_two, Nat.cast_ofNat] at heq
  have hbalance : Real.exp (-(Real.exp 1 - 1) * heatTangencyParameter 2) =
      1 - heatTangencyParameter 2 := by convert heq using 1; ring
  have h := heat_weakTypeConstant_le_formula 2 (by norm_num)
  rw [rho_two, heatBoundFormula_two_of_balanced hbalance] at h
  exact h

/-- The planar Poisson row's exact power expression at its unique tangency parameter. -/
theorem poisson_weakTypeConstant_two_le_exact :
    poissonWeakTypeConstant 2 ≤ ENNReal.ofReal
      (Real.exp 1 * poissonTangencyParameter 2 /
        (2 * (1 + poissonTangencyParameter 2) ^ (3 / 2 : ℝ)) +
          1 / (1 + Real.exp 1 * poissonTangencyParameter 2) ^ (1 / 2 : ℝ)) := by
  have hb : 0 ≤ Real.exp 1 * poissonTangencyParameter 2 :=
    mul_nonneg (Real.exp_pos _).le (poissonTangencyParameter_pos 2 (by norm_num)).le
  have h := poisson_weakTypeConstant_le_formula 2 (by norm_num)
  rw [rho_two, poissonBoundFormula_two _ hb] at h
  exact h

/-- The one-dimensional heat row's exact Gaussian-tail expression. -/
theorem heat_weakTypeConstant_one_le_exact :
    heatWeakTypeConstant 1 ≤ ENNReal.ofReal
      (4 * Real.sqrt (heatTangencyParameter 1 / Real.pi) * Real.exp (-heatTangencyParameter 1) +
        complementaryErrorFunction (2 * Real.sqrt (heatTangencyParameter 1))) := by
  have h := heat_weakTypeConstant_le_formula 1 (by norm_num)
  rw [heatBoundFormula_one_join (heatTangencyParameter_pos 1 (by norm_num)).le] at h
  exact h

/-- The one-dimensional Poisson row's exact arctangent expression. -/
theorem poisson_weakTypeConstant_one_le_exact :
    poissonWeakTypeConstant 1 ≤ ENNReal.ofReal poissonOneBound := by
  have ha : poissonTangencyParameter 1 = 1 / 5 :=
    (existsUnique_isPoissonTangencyParameter 1 (by norm_num)).unique
      (isPoissonTangencyParameter_selected 1 (by norm_num)) isPoissonTangencyParameter_one_fifth
  have h := poisson_weakTypeConstant_le_formula 1 (by norm_num)
  rw [ha, rho_one, show (4 : ℝ) * (1 / 5) = 4 / 5 by norm_num,
    poissonBoundFormula_one_fifth] at h
  exact h

end Maximal

end PartialBalayage
