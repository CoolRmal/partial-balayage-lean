/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialPlaneInterval

/-!
# Shared exact negative-power enclosures for radial tangent radii

Each positive rational radius has two genuinely checked fifth-root intervals. They
can be reused for every finite tail truncation and coordinate-difference tangent,
and soundness identifies them with the actual real negative powers.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Literal intervals for the two genuine negative powers at one positive tangent radius. -/
structure GeneratorRadialRootData where
  radius : ℚ
  radiusPower : RationalInterval
  derivativePower : RationalInterval

namespace GeneratorRadialRootData

/-- Ordinary rational fifth-power comparisons checking the actual negative powers. -/
def IsValid (D : GeneratorRadialRootData) : Prop :=
  0 < D.radius ∧
    IsPowerEnclosure D.radius (-12) D.radiusPower.lower D.radiusPower.upper ∧
    IsPowerEnclosure D.radius (-17) D.derivativePower.lower D.derivativePower.upper

instance (D : GeneratorRadialRootData) : Decidable D.IsValid := by
  unfold IsValid IsPowerEnclosure
  infer_instance

/-- The same checked roots form a genuine finite radial tangent at any difference coordinate. -/
def plane (D : GeneratorRadialRootData) (difference : ℚ) (terms : Fin 76) :
    RadialGeneratorPlaneData where
  radius := D.radius
  difference := difference
  terms := terms.val
  radiusPower := D.radiusPower
  derivativePower := D.derivativePower

/-- Root validity transfers to the actual tangent without any further analytic assumption. -/
theorem plane_valid {D : GeneratorRadialRootData} (hD : D.IsValid)
    (difference : ℚ) (terms : Fin 76) : (D.plane difference terms).IsValid := hD

/-- The shared radius interval encloses its actual real fractional power. -/
theorem radiusPower_contains {D : GeneratorRadialRootData} (hD : D.IsValid) :
    D.radiusPower.Contains ((D.radius : ℝ) ^ (-12 / 5 : ℝ)) := by
  have h := hD.2.1.rpow_bounds hD.1.le
  simpa only [RationalInterval.Contains, Int.cast_neg, Int.cast_ofNat] using h

/-- The shared derivative interval encloses its actual real fractional power. -/
theorem derivativePower_contains {D : GeneratorRadialRootData} (hD : D.IsValid) :
    D.derivativePower.Contains ((D.radius : ℝ) ^ (-17 / 5 : ℝ)) := by
  have h := hD.2.2.rpow_bounds hD.1.le
  simpa only [RationalInterval.Contains, Int.cast_neg, Int.cast_ofNat] using h

end GeneratorRadialRootData

end PartialBalayage.Maximal.Square
