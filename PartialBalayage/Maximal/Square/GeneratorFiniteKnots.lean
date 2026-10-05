/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorCellCoefficients
public import PartialBalayage.Maximal.Square.SplineGeneratorRegrouping

/-!
# Actual spline-generator assembly on the fifty-three signed knots

The genuine integer support interval is exactly the finite knot table. Combining
this equality with the closed-cell regrouping gives the actual full correction
power in finite coordinates, including all cell endpoints and signed terms.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The genuine signed knot represented by one finite table index. -/
def generatorKnot (k : Fin 53) : ℤ := (k.val : ℤ) - 26

/-- The actual integer support sum equals the fifty-three finite signed knots. -/
theorem sum_generatorKnot_eq_Icc (f : ℤ → ℝ) :
    (∑ k : Fin 53, f (generatorKnot k)) = ∑ k ∈ Finset.Icc (-26) 26, f k := by
  simp only [Int.Icc_eq_finset_map]
  norm_num only [Int.reduceAdd, Int.reduceSub, Int.reduceNeg, Int.toNat_of_nonneg]
  rw [Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  change (∑ k : Fin 53, f ((k.val : ℤ) - 26)) =
    ∑ k ∈ Finset.range 53, f (-26 + (k : ℤ))
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ f ((k : ℤ) - 26))]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

/-- Both orientations of the genuine correction use exactly the actual finite knot table. -/
theorem splineGeneratorCorrectionPower_eq_finite_knots (i j : Fin 28) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    splineGeneratorCorrectionPower ((i.val : ℝ) + t) ((j.val : ℝ) + s) =
      (∑ k : Fin 53, splineGeneratorCellPolynomial (j.val : ℤ) (generatorKnot k) s *
        |(i.val : ℝ) + t - (generatorKnot k : ℝ)| ^ (9 / 5 : ℝ)) +
      ∑ k : Fin 53, splineGeneratorCellPolynomial (i.val : ℤ) (generatorKnot k) t *
        |(j.val : ℝ) + s - (generatorKnot k : ℝ)| ^ (9 / 5 : ℝ) := by
  rw [sum_generatorKnot_eq_Icc (fun k ↦
    splineGeneratorCellPolynomial (j.val : ℤ) k s *
      |(i.val : ℝ) + t - (k : ℝ)| ^ (9 / 5 : ℝ)),
    sum_generatorKnot_eq_Icc (fun k ↦
      splineGeneratorCellPolynomial (i.val : ℤ) k t *
        |(j.val : ℝ) + s - (k : ℝ)| ^ (9 / 5 : ℝ))]
  simpa only [Int.cast_natCast] using
    splineGeneratorCorrectionPower_eq_cell_sums (i.val : ℤ) (j.val : ℤ) ht₀ ht₁ hs₀ hs₁

end PartialBalayage.Maximal.Square
