/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.AffineCellPolynomial
public import PartialBalayage.Maximal.Square.RadialCertificateBounds
public import PartialBalayage.Maximal.Square.TriangleBounds

/-!
# Soundness of an actual rational triangle majorization leaf

The rational lower polynomial uses the actual signed spline correction and genuine
downward radial height/slope. Its nonnegative Bernstein coefficients imply an inequality
for the actual kernel, including the chosen point value at the origin.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace PartialBalayage.Maximal.Square

/-- The actual rational lower polynomial after an actual affine triangle substitution. -/
def lowerPullbackPolynomial (k l : ℤ) (T : RationalTriangle)
    (q height slope target : ℚ) : MvPolynomial (Fin 2) ℚ :=
  correctionPullbackPolynomial k l T + C (height + slope * (q - (k + l) / 16) - target) -
    C (slope / 16) * (T.xPolynomial + T.yPolynomial)

/-- The actual lower polynomial has the exact total-degree-six bound. -/
theorem lowerPullbackPolynomial_totalDegree (k l : ℤ) (T : RationalTriangle)
    (q height slope target : ℚ) :
    (lowerPullbackPolynomial k l T q height slope target).totalDegree ≤ 6 := by
  have hx : T.xPolynomial.totalDegree ≤ 1 := affinePlanePolynomial_totalDegree _ _ _
  have hy : T.yPolynomial.totalDegree ≤ 1 := affinePlanePolynomial_totalDegree _ _ _
  have hlin := totalDegree_mul (C (slope / 16)) (T.xPolynomial + T.yPolynomial)
  simp only [totalDegree_C, zero_add] at hlin
  have hlin' : (C (slope / 16) * (T.xPolynomial + T.yPolynomial)).totalDegree ≤ 1 :=
    hlin.trans ((totalDegree_add _ _).trans (max_le hx hy))
  unfold lowerPullbackPolynomial
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_add _ _).trans (max_le
      (correctionPullbackPolynomial_totalDegree k l T) (by simp only [totalDegree_C]; omega))
  · exact hlin'.trans (by omega)

/-- The computed polynomial is the actual correction plus actual rational tangent terms. -/
theorem lowerPullbackPolynomial_eval (k l : ℤ) (T : RationalTriangle)
    (q height slope target : ℚ) (x y : ℝ)
    (hx₀ : 0 ≤ (T.point x y).1) (hx₁ : (T.point x y).1 ≤ 1)
    (hy₀ : 0 ≤ (T.point x y).2) (hy₁ : (T.point x y).2 ≤ 1) :
    (lowerPullbackPolynomial k l T q height slope target).eval₂ (Rat.castHom ℝ) ![x, y] =
      splineCorrection (((k : ℝ) + (T.point x y).1) / 16)
        (((l : ℝ) + (T.point x y).2) / 16) + (height : ℝ) +
          (slope : ℝ) * ((q : ℝ) -
            (((k : ℝ) + (T.point x y).1) / 16 +
              ((l : ℝ) + (T.point x y).2) / 16)) - target := by
  simp only [lowerPullbackPolynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_C,
    Rat.coe_castHom, correctionPullbackPolynomial_eval_spline k l T x y hx₀ hx₁ hy₀ hy₁,
    RationalTriangle.xPolynomial_eval, RationalTriangle.yPolynomial_eval,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  ring

/-- A checked leaf polynomial genuinely majorizes the actual kernel on its closed triangle. -/
theorem kernel_ge_target_of_lowerPullback (k l : ℕ) (T : RationalTriangle)
    (d R : RadialPowerData) (hd : d.IsValid) (hR : R.IsValid)
    (hRradius : R.radius = supportRadiusRat) (target : Fin 2)
    (hT : T.InUnitBox) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1)
    (hradius : diamondRadius (((k : ℝ) + (T.point x y).1) / 16)
      (((l : ℝ) + (T.point x y).2) / 16) ≤ (d.radius : ℝ))
    (hc : ∀ p ∈ triangleIndices, 0 ≤ triangleBernsteinCoefficient
      (planePolynomialCoefficients (lowerPullbackPolynomial k l T d.radius
        (certifiedRadialHeight d R) (certifiedRadialSlope d) target)) p.1 p.2) :
    (target : ℝ) ≤ kernel (((k : ℝ) + (T.point x y).1) / 16)
      (((l : ℝ) + (T.point x y).2) / 16) := by
  have ht := T.point_in_unitBox hT hx hy hxy
  let u := ((k : ℝ) + (T.point x y).1) / 16
  let v := ((l : ℝ) + (T.point x y).2) / 16
  have hu : 0 ≤ u := div_nonneg (add_nonneg (Nat.cast_nonneg k) ht.1) (by norm_num)
  have hv : 0 ≤ v := div_nonneg (add_nonneg (Nat.cast_nonneg l) ht.2.2.1) (by norm_num)
  by_cases hzero : u = 0 ∧ v = 0
  · rw [show kernel u v = 1 by rw [hzero.1, hzero.2, kernel_zero_zero]]
    have htarget : target.val ≤ 1 := by omega
    exact_mod_cast htarget
  have hr : 0 < diamondRadius u v := by
    simp only [diamondRadius, abs_of_nonneg hu, abs_of_nonneg hv]
    by_contra h
    have huz : u = 0 := by linarith
    have hvz : v = 0 := by linarith
    exact hzero ⟨huz, hvz⟩
  have hq : 0 < (d.radius : ℝ) := by exact_mod_cast hd.1
  have hlow := radialBase_lower_tangent hr hq hradius
    (certifiedRadialHeight_le hd hR hRradius) (certifiedRadialSlope_le hd)
  have hp := planePolynomial_nonneg_of_bernstein
    (lowerPullbackPolynomial k l T d.radius (certifiedRadialHeight d R)
      (certifiedRadialSlope d) target)
    (lowerPullbackPolynomial_totalDegree _ _ _ _ _ _ _) hc hx hy hxy
  rw [lowerPullbackPolynomial_eval _ _ _ _ _ _ _ _ _ ht.1 ht.2.1 ht.2.2.1 ht.2.2.2] at hp
  norm_num only [Int.cast_natCast, Rat.cast_natCast] at hp
  have hrEq : diamondRadius u v = u + v := by
    simp only [diamondRadius, abs_of_nonneg hu, abs_of_nonneg hv]
  rw [hrEq] at hlow
  change 0 ≤ splineCorrection u v + (certifiedRadialHeight d R : ℝ) +
    (certifiedRadialSlope d : ℝ) * ((d.radius : ℝ) - (u + v)) - (target : ℝ) at hp
  change (target : ℝ) ≤ kernel u v
  rw [kernel, ite_eq_right hzero]
  linarith

end PartialBalayage.Maximal.Square
