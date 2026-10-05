/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialPowerData
public import PartialBalayage.Maximal.Square.RadialTangent

/-!
# Actual downward height and slope bounds from the rational radial data

The rational lower-polynomial constants are connected to the actual radial tangent.
At the exact support radius the height is zero, avoiding loss from interval subtraction.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The radial coefficient as an exact rational for certificate arithmetic. -/
def radialCoefficientRat : ℚ := 11248245541992991 / 6250000000000000

/-- The support radius as an exact rational for certificate arithmetic. -/
def supportRadiusRat : ℚ := 7 / 4

theorem radialCoefficientRat_cast : (radialCoefficientRat : ℝ) = radialCoefficient := by
  norm_num [radialCoefficientRat, radialCoefficient]

theorem supportRadiusRat_cast : (supportRadiusRat : ℝ) = supportRadius := by
  norm_num [supportRadiusRat, supportRadius]

/-- The true downward rational height used on a certificate triangle. -/
def certifiedRadialHeight (d R : RadialPowerData) : ℚ :=
  if d.radius = supportRadiusRat then 0
  else radialCoefficientRat * (d.lowerSix - R.upperSix)

/-- The true downward rational slope used on a certificate triangle. -/
def certifiedRadialSlope (d : RadialPowerData) : ℚ :=
  (6 / 5) * radialCoefficientRat * d.lowerEleven

/-- Every valid exact radial row encloses the actual order-six-fifths power. -/
theorem RadialPowerData.six_bounds {d : RadialPowerData} (hd : d.IsValid) :
    (d.lowerSix : ℝ) ≤ (d.radius : ℝ) ^ (-(6 / 5 : ℝ)) ∧
      (d.radius : ℝ) ^ (-(6 / 5 : ℝ)) ≤ (d.upperSix : ℝ) := by
  have h := hd.2.1.rpow_bounds hd.1.le
  norm_num only [Int.cast_neg, Int.cast_ofNat, neg_div] at h
  exact h

/-- Every valid exact radial row encloses the actual slope power. -/
theorem RadialPowerData.eleven_bounds {d : RadialPowerData} (hd : d.IsValid) :
    (d.lowerEleven : ℝ) ≤ (d.radius : ℝ) ^ (-(11 / 5 : ℝ)) ∧
      (d.radius : ℝ) ^ (-(11 / 5 : ℝ)) ≤ (d.upperEleven : ℝ) := by
  have h := hd.2.2.rpow_bounds hd.1.le
  norm_num only [Int.cast_neg, Int.cast_ofNat, neg_div] at h
  exact h

/-- The actual certified rational height is below the actual radial tangent height. -/
theorem certifiedRadialHeight_le {d R : RadialPowerData}
    (hd : d.IsValid) (hR : R.IsValid) (hRradius : R.radius = supportRadiusRat) :
    (certifiedRadialHeight d R : ℝ) ≤ radialCoefficient *
      ((d.radius : ℝ) ^ (-(6 / 5 : ℝ)) - supportRadius ^ (-(6 / 5 : ℝ))) := by
  unfold certifiedRadialHeight
  split_ifs with h
  · rw [h, supportRadiusRat_cast, sub_self, mul_zero, Rat.cast_zero]
  · have h₀ := (RadialPowerData.six_bounds hd).1
    have h₁ := (RadialPowerData.six_bounds hR).2
    rw [hRradius, supportRadiusRat_cast] at h₁
    simp only [Rat.cast_mul, Rat.cast_sub, radialCoefficientRat_cast]
    exact mul_le_mul_of_nonneg_left (sub_le_sub h₀ h₁) radialCoefficient_pos.le

/-- The actual certified rational slope is below the actual radial tangent slope. -/
theorem certifiedRadialSlope_le {d : RadialPowerData} (hd : d.IsValid) :
    (certifiedRadialSlope d : ℝ) ≤
      (6 / 5 : ℝ) * radialCoefficient * (d.radius : ℝ) ^ (-(11 / 5 : ℝ)) := by
  have hp : 0 ≤ (6 / 5 : ℝ) * radialCoefficient :=
    mul_nonneg (by norm_num) radialCoefficient_pos.le
  simp only [certifiedRadialSlope, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    radialCoefficientRat_cast]
  exact mul_le_mul_of_nonneg_left (RadialPowerData.eleven_bounds hd).1 hp

end PartialBalayage.Maximal.Square
