/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.HessianDerivative
public import PartialBalayage.Linear.ScalarMultiplier

/-!
# The actual Beurling operator as a Hessian combination

The planar Beurling Fourier multiplier is the constant linear combination
`-H₀₀ + H₁₁ + 2i H₀₁` of the actual full Hessian multiplier. This equality holds
for every complex L² input, including the totalized zero-frequency symbols.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform

namespace PartialBalayage.Linear

/-- The constant complex linear combination of Hessian entries giving the Beurling symbol. -/
def beurlingHessianCombination : EuclideanSpace ℂ (Fin 2 × Fin 2) →L[ℂ] ℂ :=
  -hessianEntryCLM 0 0 + hessianEntryCLM 1 1 +
    (2 * Complex.I) • hessianEntryCLM 0 1

/-- The Hessian combination is exactly the article's Beurling symbol. -/
theorem beurlingHessianCombination_hessianSymbol (ξ : EuclideanSpace ℝ (Fin 2)) :
    beurlingHessianCombination (hessianSymbol ξ) = beurlingSymbol ξ := by
  change -(hessianSymbol ξ (0, 0)) + hessianSymbol ξ (1, 1) +
    (2 * Complex.I) * hessianSymbol ξ (0, 1) = _
  simp only [hessianSymbol_apply, beurlingSymbol]
  ring_nf
  simp
  ring

/-- The genuine Beurling L² operator is this constant combination of the actual Hessian. -/
theorem beurlingL2_eq_hessian_combination
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    beurlingL2 f = beurlingHessianCombination.compLp (hessianL2 f) := by
  have hfreq : beurlingHessianCombination.compLp
      (multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f)) =
        multiplyL2 beurlingSymbol measurable_beurlingSymbol norm_beurlingSymbol_le (𝓕 f) := by
    apply Lp.ext
    filter_upwards [beurlingHessianCombination.coeFn_compLp
      (multiplyVectorL2 hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f)),
      (vectorSymbol_memLp hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le
        (𝓕 f)).coeFn_toLp,
      (multiplier_memLp beurlingSymbol measurable_beurlingSymbol norm_beurlingSymbol_le
        (𝓕 f)).coeFn_toLp] with ξ hcomb hH hB
    rw [hcomb]
    change beurlingHessianCombination
      (((vectorSymbol_memLp hessianSymbol measurable_hessianSymbol norm_hessianSymbol_le
        (𝓕 f)).toLp _) ξ) = ((multiplier_memLp beurlingSymbol measurable_beurlingSymbol
          norm_beurlingSymbol_le (𝓕 f)).toLp _) ξ
    rw [hH, hB, map_smul, beurlingHessianCombination_hessianSymbol]
    simp only [smul_eq_mul, mul_comm]
  change 𝓕⁻ (multiplyL2 beurlingSymbol measurable_beurlingSymbol
      norm_beurlingSymbol_le (𝓕 f)) =
    beurlingHessianCombination.compLp (𝓕⁻ (multiplyVectorL2 hessianSymbol
      measurable_hessianSymbol norm_hessianSymbol_le (𝓕 f)))
  rw [← fourierInv_compLp, hfreq]

end PartialBalayage.Linear
