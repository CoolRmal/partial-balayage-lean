/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.IncomingCoefficientData
public import PartialBalayage.Maximal.Square.RadialPlaneInterval

/-!
# Exact Horner evaluation of the genuine finite incoming tails

The cached rational coefficients and ordinary Horner recursion evaluate
the actual finite tail polynomials and their actual derivatives. Generic
proved equalities connect every bounded term count and rational point to
the original sums; no finite-evaluation proposition is assumed.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- Ordinary exact Horner recursion for a finite rational coefficient family. -/
def incomingHorner (c : ℕ → ℚ) (N : ℕ) (x : ℚ) : ℚ :=
  match N with
  | 0 => 0
  | n + 1 => c 0 + x * incomingHorner (fun k ↦ c (k + 1)) n x

/-- The genuine recursive evaluation equals the original finite polynomial sum. -/
theorem incomingHorner_eq (c : ℕ → ℚ) (N : ℕ) (x : ℚ) :
    incomingHorner c N x = rationalRadialValue c N x := by
  induction N generalizing c with
  | zero => simp [incomingHorner, rationalRadialValue]
  | succ n ih =>
    rw [incomingHorner, ih]
    unfold rationalRadialValue
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    rw [Finset.mul_sum]
    rw [add_comm (∑ k ∈ Finset.range n, c (k + 1) * x ^ (k + 1))]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring

private theorem incomingHorner_derivative_eq (c : ℕ → ℚ) (N : ℕ) (x : ℚ) :
    incomingHorner (fun k ↦ c (k + 1) * (k + 1)) (N - 1) x =
      rationalRadialDerivative c N x := by
  cases N with
  | zero => simp [incomingHorner, rationalRadialDerivative]
  | succ n =>
    rw [Nat.add_sub_cancel, incomingHorner_eq]
    unfold rationalRadialValue rationalRadialDerivative
    rw [Finset.sum_range_succ']
    simp

/-- The cached even family retains exactly the original integrated even coefficients. -/
def cachedIncomingEvenCoefficient (n : ℕ) : ℚ :=
  if Even n then cachedIncomingCoefficient n else 0

theorem cachedIncomingEvenCoefficient_eq {n : ℕ} (hn : n < 75) :
    cachedIncomingEvenCoefficient n = radialEvenCoefficient n := by
  unfold cachedIncomingEvenCoefficient radialEvenCoefficient
  rw [cachedIncomingCoefficient_eq hn]

/-- Fast exact evaluation of the actual incoming tail at all supported term counts. -/
def incomingTailValue (N : Fin 76) (x : ℚ) : ℚ :=
  incomingHorner cachedIncomingCoefficient N.val x

/-- Fast exact evaluation of the actual incoming-tail derivative. -/
def incomingTailDerivative (N : Fin 76) (x : ℚ) : ℚ :=
  incomingHorner (fun k ↦ cachedIncomingCoefficient (k + 1) * (k + 1)) (N.val - 1) x

/-- Fast exact evaluation of the actual even incoming tail. -/
def incomingEvenTailValue (N : Fin 76) (x : ℚ) : ℚ :=
  incomingHorner cachedIncomingEvenCoefficient N.val x

/-- Fast exact evaluation of the actual even incoming-tail derivative. -/
def incomingEvenTailDerivative (N : Fin 76) (x : ℚ) : ℚ :=
  incomingHorner (fun k ↦ cachedIncomingEvenCoefficient (k + 1) * (k + 1)) (N.val - 1) x

private theorem rationalRadialValue_cache_eq (c d : ℕ → ℚ) (N : Fin 76) (x : ℚ)
    (h : ∀ n, n < 75 → c n = d n) :
    rationalRadialValue c N.val x = rationalRadialValue d N.val x := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n (by have := N.isLt; have := Finset.mem_range.mp hn; omega)]

private theorem rationalRadialDerivative_cache_eq (c d : ℕ → ℚ) (N : Fin 76) (x : ℚ)
    (h : ∀ n, n < 75 → c n = d n) :
    rationalRadialDerivative c N.val x = rationalRadialDerivative d N.val x := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n (by have := N.isLt; have := Finset.mem_range.mp hn; omega)]

/-- Exact generic equality with the actual original incoming-tail sum. -/
theorem incomingTailValue_eq (N : Fin 76) (x : ℚ) :
    incomingTailValue N x = rationalRadialValue radialIncomingCoefficient N.val x := by
  rw [incomingTailValue, incomingHorner_eq]
  exact rationalRadialValue_cache_eq _ _ N x (fun _ hn ↦ cachedIncomingCoefficient_eq hn)

/-- Exact generic equality with the actual original incoming-tail derivative. -/
theorem incomingTailDerivative_eq (N : Fin 76) (x : ℚ) :
    incomingTailDerivative N x = rationalRadialDerivative radialIncomingCoefficient N.val x := by
  rw [incomingTailDerivative, incomingHorner_derivative_eq]
  exact rationalRadialDerivative_cache_eq _ _ N x
    (fun _ hn ↦ cachedIncomingCoefficient_eq hn)

/-- Exact generic equality with the actual original even-tail sum. -/
theorem incomingEvenTailValue_eq (N : Fin 76) (x : ℚ) :
    incomingEvenTailValue N x = rationalRadialValue radialEvenCoefficient N.val x := by
  rw [incomingEvenTailValue, incomingHorner_eq]
  exact rationalRadialValue_cache_eq _ _ N x
    (fun _ hn ↦ cachedIncomingEvenCoefficient_eq hn)

/-- Exact generic equality with the actual original even-tail derivative. -/
theorem incomingEvenTailDerivative_eq (N : Fin 76) (x : ℚ) :
    incomingEvenTailDerivative N x = rationalRadialDerivative radialEvenCoefficient N.val x := by
  rw [incomingEvenTailDerivative, incomingHorner_derivative_eq]
  exact rationalRadialDerivative_cache_eq _ _ N x
    (fun _ hn ↦ cachedIncomingEvenCoefficient_eq hn)

end PartialBalayage.Maximal.Square
