/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.MajorizationLeaf
public import PartialBalayage.Maximal.Square.ArrayPolynomial

/-!
# Pointwise soundness of the checked triangle data

Three rational vertex inequalities discharge the radius bound in the actual kernel
majorization theorem. The conclusion holds at every point of the closed real triangle.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Bounded ordinary kernel checks cover every genuine degree-six Bernstein index. -/
theorem triangleBernstein_nonneg_of_fin_checks (c : ℕ × ℕ → ℚ)
    (hc : ∀ a b : Fin 7, a.val + b.val ≤ 6 →
      0 ≤ triangleBernsteinCoefficient c a.val b.val) :
    ∀ p ∈ triangleIndices, 0 ≤ triangleBernsteinCoefficient c p.1 p.2 := by
  intro p hp
  have h := mem_triangleIndices.mp hp
  exact hc ⟨p.1, by omega⟩ ⟨p.2, by omega⟩ h

/-- The three exact rational radius checks for a grid triangle. -/
def RationalTriangle.HasRadiusBound (T : RationalTriangle) (k l : ℕ) (q : ℚ) : Prop :=
  (k + l : ℚ) + T.v₀.1 + T.v₀.2 ≤ 16 * q ∧
    (k + l : ℚ) + T.v₁.1 + T.v₁.2 ≤ 16 * q ∧
      (k + l : ℚ) + T.v₂.1 + T.v₂.2 ≤ 16 * q

/-- The vertex checks give the true radius bound on the actual quarter-grid image. -/
theorem RationalTriangle.diamondRadius_le_of_vertices (T : RationalTriangle)
    (k l : ℕ) {q : ℚ} (hT : T.InUnitBox) (hq : T.HasRadiusBound k l q)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    diamondRadius (((k : ℝ) + (T.point x y).1) / 16)
      (((l : ℝ) + (T.point x y).2) / 16) ≤ (q : ℝ) := by
  have ht := T.point_in_unitBox hT hx hy hxy
  have hu : 0 ≤ ((k : ℝ) + (T.point x y).1) / 16 :=
    div_nonneg (add_nonneg (Nat.cast_nonneg k) ht.1) (by norm_num)
  have hv : 0 ≤ ((l : ℝ) + (T.point x y).2) / 16 :=
    div_nonneg (add_nonneg (Nat.cast_nonneg l) ht.2.2.1) (by norm_num)
  have hs := T.point_sum_le (q := 16 * q - (k + l : ℚ))
    (by linarith [hq.1]) (by linarith [hq.2.1]) (by linarith [hq.2.2]) hx hy hxy
  push_cast at hs
  rw [diamondRadius, abs_of_nonneg hu, abs_of_nonneg hv]
  linarith

/-- An ordinary checked array certifies the actual kernel on the entire closed triangle. -/
theorem kernel_ge_target_on_checked_triangle (k l : ℕ) (T : RationalTriangle)
    (d R : RadialPowerData) (hd : d.IsValid) (hR : R.IsValid)
    (hRradius : R.radius = supportRadiusRat) (target : Fin 2)
    (hT : T.InUnitBox) (hr : T.HasRadiusBound k l d.radius)
    (c : ℕ × ℕ → ℚ)
    (heq : lowerPullbackPolynomial k l T d.radius
      (certifiedRadialHeight d R) (certifiedRadialSlope d) target = planeArrayPolynomial c)
    (hc : ∀ p ∈ triangleIndices, 0 ≤ triangleBernsteinCoefficient c p.1 p.2)
    {p : ℝ × ℝ} (hp : T.Contains p) :
    (target : ℝ) ≤ kernel (((k : ℝ) + p.1) / 16) (((l : ℝ) + p.2) / 16) := by
  rcases hp with ⟨x, y, hx, hy, hxy, rfl⟩
  apply kernel_ge_target_of_lowerPullback k l T d R hd hR hRradius target hT hx hy hxy
    (T.diamondRadius_le_of_vertices k l hT hr hx hy hxy)
  intro p hp
  rw [heq, planeArrayPolynomial_bernsteinCoefficient]
  exact hc p hp

end PartialBalayage.Maximal.Square
