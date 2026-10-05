/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialPlaneInterval
public import PartialBalayage.Maximal.Square.Data.GeneratorScaleData

/-!
# Checked genuine first radial tangent data

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- The actual first source rectangle uses the positive boundary tangent radius. -/
def generatorRadialPlane0 : RadialGeneratorPlaneData where
  radius := (7 / 4 : ℚ)
  difference := (55 / 32 : ℚ)
  terms := 0
  radiusPower := generatorRadiusInterval
  derivativePower :=
    ⟨
      (189090713623552286808883383573 / 1267650600228229401496703205376 : ℚ),
      (94545356811776143404441691787 / 633825300114114700748351602688 : ℚ)⟩

/-- Both genuine negative powers pass ordinary exact fifth-power checks. -/
theorem generatorRadialPlane0_valid : generatorRadialPlane0.IsValid := by
  unfold RadialGeneratorPlaneData.IsValid IsPowerEnclosure generatorRadialPlane0
  unfold generatorRadiusInterval
  decide +kernel

end PartialBalayage.Maximal.Square
