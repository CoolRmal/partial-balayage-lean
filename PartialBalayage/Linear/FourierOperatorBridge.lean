/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierOperatorDefinitions
public import PartialBalayage.Linear.HessianLinearity
public import PartialBalayage.Linear.TracelessMultiplier
public import PartialBalayage.Linear.ScalarMultiplier
public import PartialBalayage.Linear.ProjectionMultiplier

/-!
# Concrete independent Fourier operators agree with actual bounded multipliers

The selected frequency class in the independent definitions exists because the true
bounded-symbol action belongs to L². Almost-everywhere equality of representatives
then gives equality of the L² classes and their inverse Fourier transforms.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

section General

variable {n : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An actual frequency representative determines the independently selected Fourier class. -/
theorem canonicalL2FourierOperator_eq_of_frequency_class
    (m : EuclideanSpace ℝ (Fin n) → E → F)
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (g : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : ∀ᵐ ξ, g ξ = m ξ ((𝓕 f : Lp E 2 volume) ξ)) :
    canonicalL2FourierOperator m f =
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F).symm g := by
  have heq : Classical.epsilon (fun h : Lp F 2 volume ↦
      ∀ᵐ ξ, h ξ = m ξ ((𝓕 f : Lp E 2 volume) ξ)) = g := by
    have hp : ∀ᵐ ξ, (Classical.epsilon (fun h : Lp F 2 volume ↦
        ∀ᵐ ξ, h ξ = m ξ ((𝓕 f : Lp E 2 volume) ξ))) ξ =
          m ξ ((𝓕 f : Lp E 2 volume) ξ) :=
      Classical.epsilon_spec (p := fun h : Lp F 2 volume ↦
        ∀ᵐ ξ, h ξ = m ξ ((𝓕 f : Lp E 2 volume) ξ)) ⟨g, hg⟩
    apply Lp.ext
    filter_upwards [hp, hg] with ξ hx hy
    exact hx.trans hy.symm
  simp only [canonicalL2FourierOperator, heq]

/-- The independent definition agrees with a genuine bounded operator-valued multiplier. -/
theorem canonicalL2FourierOperator_eq_operatorMultiplier
    (m : EuclideanSpace ℝ (Fin n) → E →L[ℂ] F)
    (hm : AEStronglyMeasurable m volume) (M : ℝ≥0)
    (hb : ∀ ξ, ‖m ξ‖ ≤ (M : ℝ))
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    canonicalL2FourierOperator (fun ξ z ↦ m ξ z) f =
      operatorMultiplierL2CLM m hm M hb f := by
  exact canonicalL2FourierOperator_eq_of_frequency_class _ f _
    (multiplyOperatorL2_ae m hm M hb (𝓕 f))

end General

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The independent definition agrees with the genuine Euclidean-vector multiplier. -/
theorem canonicalL2FourierOperator_eq_vectorMultiplier
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι)
    (hm : Measurable m) (hb : ∀ ξ, ‖m ξ‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    canonicalL2FourierOperator (fun ξ z ↦ z • m ξ) f =
      vectorMultiplierL2 m hm hb f := by
  exact canonicalL2FourierOperator_eq_of_frequency_class _ f _
    ((vectorSymbol_memLp m hm hb (𝓕 f)).coeFn_toLp)

/-- The independent definition agrees with a vector multiplier of any finite norm bound. -/
theorem canonicalL2FourierOperator_eq_boundedVectorMultiplier
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ ι)
    (hm : Measurable m) (M : ℝ≥0) (hb : ∀ ξ, ‖m ξ‖ ≤ (M : ℝ))
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    canonicalL2FourierOperator (fun ξ z ↦ z • m ξ) f =
      boundedVectorMultiplierL2CLM m hm M hb f := by
  exact canonicalL2FourierOperator_eq_of_frequency_class _ f _
    ((boundedVectorSymbol_memLp m hm M hb (𝓕 f)).coeFn_toLp)

/-- The independent definition agrees with the genuine scalar Fourier multiplier. -/
theorem canonicalL2FourierOperator_eq_scalarMultiplier
    (m : EuclideanSpace ℝ (Fin n) → ℂ) (hm : Measurable m)
    (hb : ∀ ξ, ‖m ξ‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    canonicalL2FourierOperator (fun ξ z ↦ m ξ * z) f = scalarMultiplierL2 m hm hb f := by
  exact canonicalL2FourierOperator_eq_of_frequency_class _ f _
    ((multiplier_memLp m hm hb (𝓕 f)).coeFn_toLp)

/-- The independent full real-input Riesz vector is the actual full Euclidean Riesz transform. -/
theorem rieszFourierOperator_eq_rieszL2
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    rieszFourierOperator f = rieszL2 (Complex.ofRealCLM.compLp f) := by
  exact canonicalL2FourierOperator_eq_vectorMultiplier rieszSymbol measurable_rieszSymbol
    norm_rieszSymbol_le (Complex.ofRealCLM.compLp f)

/-- The independent full complex-input Beurling operator is the actual Beurling multiplier. -/
theorem beurlingFourierOperator_eq_beurlingL2
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    beurlingFourierOperator f = beurlingL2 f := by
  exact canonicalL2FourierOperator_eq_scalarMultiplier beurlingSymbol measurable_beurlingSymbol
    norm_beurlingSymbol_le f

/-- The independent Hessian acts by the actual full Frobenius-matrix transform. -/
theorem hessianFourierOperator_eq_hessianL2
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    hessianFourierOperator f = hessianL2 f := by
  exact canonicalL2FourierOperator_eq_vectorMultiplier hessianSymbol measurable_hessianSymbol
    norm_hessianSymbol_le f

/-- The independent traceless Hessian acts by the actual bounded Frobenius-matrix transform. -/
theorem tracelessHessianFourierOperator_eq_tracelessHessianL2CLM (hn : 0 < n)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    tracelessHessianFourierOperator f = tracelessHessianL2CLM n hn f := by
  exact canonicalL2FourierOperator_eq_boundedVectorMultiplier tracelessHessianSymbol
    measurable_tracelessHessianSymbol _ (norm_tracelessHessianSymbol_le hn) f

/-- The concrete gradient action is precisely the genuine orthogonal projection symbol. -/
theorem gradientFourierAction_eq (ξ : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : gradientFourierAction ξ z = gradientProjectionSymbol ξ z := by
  simp only [gradientFourierAction, gradientProjectionSymbol, smul_apply,
    InnerProductSpace.rankOne_apply, complexifyEuclidean]

/-- The independent gradient projection is the actual bounded projection multiplier. -/
theorem gradientFourierOperator_eq_gradientProjectionL2CLM
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    gradientFourierOperator f = gradientProjectionL2CLM f := by
  unfold gradientFourierOperator
  rw [show gradientFourierAction = (fun ξ z ↦ gradientProjectionSymbol ξ z) from
    funext (fun ξ ↦ funext (gradientFourierAction_eq ξ))]
  exact canonicalL2FourierOperator_eq_operatorMultiplier gradientProjectionSymbol
    measurable_gradientProjectionSymbol.aestronglyMeasurable 1 norm_gradientProjectionSymbol_le f

/-- The independent Leray projection is the actual bounded complementary projection. -/
theorem lerayFourierOperator_eq_lerayProjectionL2CLM
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    lerayFourierOperator f = lerayProjectionL2CLM f := by
  unfold lerayFourierOperator
  simp_rw [gradientFourierAction_eq]
  exact canonicalL2FourierOperator_eq_operatorMultiplier lerayProjectionSymbol
    measurable_lerayProjectionSymbol.aestronglyMeasurable 1 norm_lerayProjectionSymbol_le f

end PartialBalayage.Linear
