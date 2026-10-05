/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonL2Fourier

/-!
# Self-adjointness of genuine Poisson averaging

The actual normalized spatial operator is self-adjoint on Hilbert `L²`, because its exact
Fourier symbol is real. Consequently its actual difference quotient can be moved onto a test.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform

namespace PartialBalayage.Linear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

local instance poissonSelfAdjointRealSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
local instance poissonSelfAdjointScalarTower : IsScalarTower ℝ ℂ E :=
  IsScalarTower.restrictScalars ℝ ℂ E

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp E 2 (volume : Measure D)

/-- The genuine spatial Poisson operator is self-adjoint on the actual Hilbert `L²` space. -/
theorem inner_poissonConvolutionL2 {t : ℝ} (ht : 0 < t) (f g : L²) :
    inner ℂ f (poissonConvolutionL2 ht g) = inner ℂ (poissonConvolutionL2 ht f) g := by
  rw [← (Lp.fourierTransformₗᵢ D E).inner_map_map f (poissonConvolutionL2 ht g),
    ← (Lp.fourierTransformₗᵢ D E).inner_map_map (poissonConvolutionL2 ht f) g]
  change inner ℂ (𝓕 f) (𝓕 (poissonConvolutionL2 ht g)) =
    inner ℂ (𝓕 (poissonConvolutionL2 ht f)) (𝓕 g)
  rw [fourier_poissonConvolutionL2 ht, fourier_poissonConvolutionL2 ht,
    L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplyOperatorL2_ae (poissonOperatorSymbol t)
    (aestronglyMeasurable_poissonOperatorSymbol t) 1
    (norm_poissonOperatorSymbol_le ht.le) (𝓕 f),
    multiplyOperatorL2_ae (poissonOperatorSymbol t)
      (aestronglyMeasurable_poissonOperatorSymbol t) 1
      (norm_poissonOperatorSymbol_le ht.le) (𝓕 g)] with ξ hf hg
  rw [hf, hg]
  simp only [poissonOperatorSymbol, smul_apply,
    ContinuousLinearMap.id_apply, inner_smul_right, inner_smul_left, Complex.conj_ofReal]

/-- The actual positive-height Poisson difference quotient on any `L²` input. -/
def poissonQuotientL2 {t : ℝ} (ht : 0 < t) (f : L²) : L² :=
  (t⁻¹ : ℂ) • (f - poissonConvolutionL2 ht f)

/-- The actual Poisson quotient can be moved onto any genuine `L²` test. -/
theorem inner_poissonQuotientL2 {t : ℝ} (ht : 0 < t) (f g : L²) :
    inner ℂ f (poissonQuotientL2 ht g) = inner ℂ (poissonQuotientL2 ht f) g := by
  rw [poissonQuotientL2, poissonQuotientL2, inner_smul_right, inner_smul_left,
    inner_sub_right, inner_sub_left, inner_poissonConvolutionL2 ht f g,
    ← Complex.ofReal_inv, Complex.conj_ofReal]

end PartialBalayage.Linear
