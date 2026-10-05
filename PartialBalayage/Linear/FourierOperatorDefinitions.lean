/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Independent concrete Fourier operators and full L¹ weak constants

The multiplier operators are specified directly by their Fourier symbols. A selected
frequency class agrees almost everywhere with the actual symbol action; this class exists
for every bounded symbol used below, as proved in the implementation bridge. No symbol
bound or analytical certificate is a hypothesis of these operator definitions.

The weak constant quantifies over linear all-L¹ extensions agreeing with the specified
L² operator. A weak bound implies convergence-in-measure continuity, so the true extension
is unique by L¹ density of L¹ and L². The genuine extension theorem supplies these maps.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal

namespace PartialBalayage

section Fourier

variable {n : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The exact inverse Fourier transform of the actual symbol action on the Fourier input. -/
def canonicalL2FourierOperator
    (m : EuclideanSpace ℝ (Fin n) → E → F)
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F).symm
    (Classical.epsilon (fun g : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ↦
      ∀ᵐ ξ, g ξ = m ξ ((𝓕 f : Lp E 2 volume) ξ)))

end Fourier

/-- The full Euclidean vector Riesz symbol with its harmless zero-frequency value. -/
def fourierRieszSymbol {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  (Complex.I / (‖ξ‖ : ℂ)) • WithLp.toLp 2 (fun i ↦ (ξ i : ℂ))

/-- The full Riesz vector transform on real input, defined by its actual Fourier symbol. -/
def rieszFourierOperator {n : ℕ}
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z • fourierRieszSymbol ξ)
    (Complex.ofRealCLM.compLp f)

/-- The complex-input planar Beurling multiplier. -/
def beurlingFourierOperator
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) :=
  canonicalL2FourierOperator
    (fun ξ z ↦ (((ξ 0 : ℂ) - (ξ 1 : ℂ) * Complex.I) ^ 2 / (‖ξ‖ ^ 2 : ℂ)) * z) f

/-- The full second-order Riesz matrix symbol, with its genuine Frobenius norm. -/
def fourierHessianSymbol {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  ((-1 : ℂ) / (‖ξ‖ : ℂ) ^ (2 : ℕ)) •
    WithLp.toLp 2 (fun ij ↦ (ξ ij.1 : ℂ) * (ξ ij.2 : ℂ))

/-- The full Frobenius-matrix Hessian transform defined by its actual Fourier symbol. -/
def hessianFourierOperator {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z • fourierHessianSymbol ξ) f

/-- The traceless full Frobenius-matrix transform defined by its actual Fourier symbol. -/
def tracelessHessianFourierOperator {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z •
    (if ξ = 0 then 0 else fourierHessianSymbol ξ + ((n : ℂ)⁻¹) •
      WithLp.toLp 2 (fun ij : Fin n × Fin n ↦ if ij.1 = ij.2 then 1 else 0))) f

/-- The true gradient projection action on a complex Euclidean frequency vector. -/
def gradientFourierAction {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  ((‖ξ‖ ^ (2 : ℕ) : ℝ)⁻¹ : ℂ) •
    (inner ℂ (WithLp.toLp 2 (fun i ↦ (ξ i : ℂ))) z •
      WithLp.toLp 2 (fun i ↦ (ξ i : ℂ)))

/-- The actual gradient projection on vector fields, defined directly in Fourier space. -/
def gradientFourierOperator {n : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator gradientFourierAction f

/-- The actual Leray projection on vector fields, defined directly in Fourier space. -/
def lerayFourierOperator {n : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z - gradientFourierAction ξ z) f

section WeakConstants

variable {X E F 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A genuine linear all-L¹ extension, with exact L² agreement and every-level weak bound. -/
def IsLinearWeakTypeBound (T₂ : Lp E 2 μ → Lp F 2 μ) (C : ℝ≥0∞) : Prop :=
  ∃ T₁ : Lp E 1 μ →ₗ[𝕜] AEEqFun X F μ,
    (∀ (f₁ : Lp E 1 μ) (f₂ : Lp E 2 μ), (f₁ : X → E) =ᵐ[μ] f₂ →
      (T₁ f₁ : X → F) =ᵐ[μ] T₂ f₂) ∧
    ∀ (f₁ : Lp E 1 μ) (α : ℝ≥0∞),
      α * μ {x | α < ‖T₁ f₁ x‖ₑ} ≤ C * ∫⁻ x, ‖f₁ x‖ₑ ∂μ

/-- The true weak constant of the canonical all-L¹ extension of the specified L² operator. -/
def linearWeakTypeConstant (T₂ : Lp E 2 μ → Lp F 2 μ) : ℝ≥0∞ :=
  sInf {C | IsLinearWeakTypeBound (𝕜 := 𝕜) T₂ C}

end WeakConstants

end PartialBalayage
