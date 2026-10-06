/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Independent concrete operators and exact table constants
All mathematical definitions used by the compared statements occupy one standalone
Mathlib-only module. The same transparent block is repeated in `Challenge.lean`.
This keeps generated volume-instance proof sharing identical across the environments.
No analytical certificate or solution theorem determines any operator or constant.
-/
@[expose] public section

noncomputable section

open MeasureTheory Metric Set FourierTransform
open scoped ENNReal
namespace PartialBalayage
/-- The centred maximal function over axis-parallel cubes of side `2r`. -/
def cubeMaximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ
def IsCubeWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : (Fin d → ℝ) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < cubeMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ
def cubeWeakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsCubeWeakTypeBound d C}
/-- The centred maximal function over open Euclidean balls of radius `r`. -/
def ballMaximalFunction {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
def IsBallWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < ballMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ
def ballWeakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsBallWeakTypeBound d C}
def poissonKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) *
    t / (t ^ 2 + ‖x‖ ^ 2) ^ (((n : ℝ) + 1) / 2)
def heatKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))
def poissonMaximalFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), ∫⁻ y, ENNReal.ofReal (poissonKernel n t (x - y)) * ‖f y‖ₑ
def heatMaximalFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), ∫⁻ y, ENNReal.ofReal (heatKernel n t (x - y)) * ‖f y‖ₑ
def IsPoissonWeakTypeBound (n : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < poissonMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ
def IsHeatWeakTypeBound (n : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < heatMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ
def poissonWeakTypeConstant (n : ℕ) : ℝ≥0∞ := sInf {C | IsPoissonWeakTypeBound n C}
def heatWeakTypeConstant (n : ℕ) : ℝ≥0∞ := sInf {C | IsHeatWeakTypeBound n C}
def poissonBoundFormula (n : ℕ) (a b : ℝ) : ℝ :=
  Real.Gamma (((n : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((n : ℝ) / 2)) *
    (2 * b ^ ((n : ℝ) / 2) / ((n : ℝ) * (1 + a) ^ (((n : ℝ) + 1) / 2)) +
      ∫ z in Set.Ioi b, z ^ ((n : ℝ) / 2 - 1) / (1 + z) ^ (((n : ℝ) + 1) / 2))
def heatBoundFormula (n : ℕ) (a b : ℝ) : ℝ :=
  (Real.Gamma ((n : ℝ) / 2))⁻¹ *
    (2 * b ^ ((n : ℝ) / 2) * Real.exp (-a) / (n : ℝ) +
      ∫ z in Set.Ioi b, z ^ ((n : ℝ) / 2 - 1) * Real.exp (-z))
def poissonOneBound : ℝ :=
  1 + 2 / Real.pi * (Real.sqrt 5 / 3 - Real.arctan (2 / Real.sqrt 5))
namespace Constants
def rho (n : ℕ) : ℝ :=
  if n = 2 then Real.exp 1 else ((n : ℝ) / 2) ^ (2 / ((n : ℝ) - 2))
end Constants
open Constants
def IsHeatTangencyParameter (n : ℕ) (a : ℝ) : Prop :=
  a ∈ Ioo ((n : ℝ) / (2 * rho n)) ((n : ℝ) / 2) ∧
    Real.exp (-(rho n - 1) * a) = 1 - 2 * a / (n : ℝ)
def IsPoissonTangencyParameter (n : ℕ) (a : ℝ) : Prop :=
  a ∈ Ioo ((n : ℝ) / (3 * rho n)) ((n : ℝ) / 3) ∧
    (1 - a / (n : ℝ)) / (1 + a) ^ (((n : ℝ) + 3) / 2) =
      1 / (1 + rho n * a) ^ (((n : ℝ) + 1) / 2)
def heatTangencyParameter (n : ℕ) : ℝ := Classical.epsilon (IsHeatTangencyParameter n)
def poissonTangencyParameter (n : ℕ) : ℝ := Classical.epsilon (IsPoissonTangencyParameter n)
def complementaryErrorFunction (r : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ s in Set.Ioi r, Real.exp (-(s ^ 2))
end PartialBalayage

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
/-- The full complex-input Riesz vector, defined by its genuine Fourier symbol. -/
def complexRieszFourierOperator {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z • fourierRieszSymbol ξ) f
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

namespace PartialBalayage
def hessianParameter (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) /
    ((n : ℝ) + 1 + Real.sqrt (((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2))))
def hessianCoefficient (n : ℕ) (a : ℝ) : ℝ :=
  1 / a + ((n : ℝ) - 1) * a / ((n : ℝ) - a ^ 2)
def projectionCubic (a : ℝ) : ℝ := a ^ 3 - 2 * a ^ 2 + 6 * a - 4
/-- The unique cubic root in `(0,1)`, whose existence and uniqueness are proved separately. -/
def projectionParameter : ℝ :=
  Classical.epsilon (fun a : ℝ ↦ a ∈ Set.Ioo 0 1 ∧ projectionCubic a = 0)
def projectionCoefficient (a : ℝ) : ℝ := 1 / a + a / (2 - a) ^ 2
end PartialBalayage

open PartialBalayage.Constants

namespace PartialBalayage

/-- The table's interval bound: the centred weak type `(1,1)` constant is at most `2`. -/
theorem interval_weakTypeConstant_le_two : cubeWeakTypeConstant 1 ≤ 2 := by
  sorry

/-- The table's planar Euclidean-ball bound: the centred weak type constant is at most `e`. -/
theorem ball_weakTypeConstant_two_le_exp :
    ballWeakTypeConstant 2 ≤ ENNReal.ofReal (Real.exp 1) := by
  sorry

/-- The table's Euclidean-ball bound in every dimension `n ≥ 3`. -/
theorem ball_weakTypeConstant_le_rpow (n : ℕ) (hn : 3 ≤ n) :
    ballWeakTypeConstant n ≤
      ENNReal.ofReal (((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))) := by
  sorry
/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    heatWeakTypeConstant n ≤ ENNReal.ofReal
      (heatBoundFormula n (heatTangencyParameter n) (rho n * heatTangencyParameter n)) := by
  sorry

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_le_formula (n : ℕ) (hn : 1 ≤ n) :
    poissonWeakTypeConstant n ≤ ENNReal.ofReal
      (poissonBoundFormula n (poissonTangencyParameter n)
        (rho n * poissonTangencyParameter n)) := by
  sorry

/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_two_le_exact :
    heatWeakTypeConstant 2 ≤ ENNReal.ofReal
      ((1 + (Real.exp 1 - 1) * heatTangencyParameter 2) * Real.exp (-heatTangencyParameter 2)) := by
  sorry

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_two_le_exact :
    poissonWeakTypeConstant 2 ≤ ENNReal.ofReal
      (Real.exp 1 * poissonTangencyParameter 2 /
        (2 * (1 + poissonTangencyParameter 2) ^ (3 / 2 : ℝ)) +
          1 / (1 + Real.exp 1 * poissonTangencyParameter 2) ^ (1 / 2 : ℝ)) := by
  sorry

/-- The exact heat table bound for the indicated dimension. -/
theorem heat_weakTypeConstant_one_le_exact :
    heatWeakTypeConstant 1 ≤ ENNReal.ofReal
      (4 * Real.sqrt (heatTangencyParameter 1 / Real.pi) * Real.exp (-heatTangencyParameter 1) +
        complementaryErrorFunction (2 * Real.sqrt (heatTangencyParameter 1))) := by
  sorry

/-- The exact Poisson table bound for the indicated dimension. -/
theorem poisson_weakTypeConstant_one_le_exact :
    poissonWeakTypeConstant 1 ≤ ENNReal.ofReal poissonOneBound := by
  sorry

/-- The full Frobenius Hessian's exact all-L¹ bound in every dimension at least two. -/
theorem hessian_weakTypeConstant_le_formula (n : ℕ) (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianFourierOperator (n := n)) ≤
      ENNReal.ofReal (hessianCoefficient n (hessianParameter n)) := by
  sorry

/-- The full planar Frobenius Hessian's exact coefficient is `3 * sqrt 6 / 4`. -/
theorem hessian_weakTypeConstant_two_le_exact :
    linearWeakTypeConstant (𝕜 := ℂ) (hessianFourierOperator (n := 2)) ≤
      ENNReal.ofReal (3 * Real.sqrt 6 / 4) := by
  sorry

/-- The actual complex-input Beurling transform has all-L¹ weak coefficient at most two. -/
theorem beurling_weakTypeConstant_le_two :
    linearWeakTypeConstant (𝕜 := ℂ) beurlingFourierOperator ≤ 2 := by
  sorry

/-- The full traceless Frobenius Hessian has the dimension-dependent table coefficient. -/
theorem tracelessHessian_weakTypeConstant_le (n : ℕ) (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (tracelessHessianFourierOperator (n := n)) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - 1 / (n : ℝ))) := by
  sorry

/-- Both actual projections have the same exact cubic-root coefficient on all L¹ inputs. -/
theorem projections_weakTypeConstants_le_exact (n : ℕ) (hn : 2 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (gradientFourierOperator (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) ∧
    linearWeakTypeConstant (𝕜 := ℂ) (lerayFourierOperator (n := n)) ≤
      ENNReal.ofReal (projectionCoefficient projectionParameter) := by
  sorry

/-- The complete complex-input Riesz vector has coefficient two on every complex L¹ input. -/
theorem riesz_weakTypeConstant_le_two (n : ℕ) (hn : 1 ≤ n) :
    linearWeakTypeConstant (𝕜 := ℂ) (complexRieszFourierOperator (n := n)) ≤ 2 := by
  sorry


/-- The centered square maximal operator has weak-type constant strictly below 3.616. -/
theorem square_weakTypeConstant_lt_3_616 :
    cubeWeakTypeConstant 2 < ENNReal.ofReal (452 / 125 : ℝ) := by
  sorry

end PartialBalayage
