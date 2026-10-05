/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorTensorApproximation
public import PartialBalayage.Maximal.Square.RadialRectangleTangent
public import PartialBalayage.Maximal.Square.Data.GeneratorScaleData
public import PartialBalayage.Maximal.Square.Data.GeneratorCubicInterval_27_1_1
public import PartialBalayage.Maximal.Square.Data.GeneratorCubicInterval_0_1_0
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerFamily_27_1_1
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerFamily_0_1_0
public import PartialBalayage.Maximal.Square.Data.GeneratorRadialPlane0

/-!
# Exact arithmetic for the first actual generator rectangle

This inequality computes the genuine interval assembly from the separately
checked cubic, power, radial, and scaling data. It uses no tail terms: the actual
nonnegative incoming tail is omitted. Pointwise soundness is assembled separately.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual assembled intervals of the first dyadic rectangle's tensor polynomial. -/
def firstGeneratorLeafIntervals (p : RectangleIndex) : RationalInterval :=
  (splineGeneratorFactorInterval.nonnegMul
    (generatorApproximationIntervals generatorCubicData_27_1_1 generatorCubicData_0_1_0
      generatorPowerFamily_27_1_1 generatorPowerFamily_0_1_0 p)).add
    (radialRectangleIntervals generatorRadialPlane0 (125337337 / 50000000)
      generatorRadiusInterval.lower (7 / 4) (11248245541992991 / 6250000000000000)
      (111 / 4) (1 / 4) (111 / 4) (1 / 4) p)

/-- Actual error bound for the same closed rectangle, including the positive scale interval. -/
def firstGeneratorLeafError : ℚ :=
  splineGeneratorFactorInterval.upper *
    generatorApproximationError generatorCubicData_27_1_1 generatorCubicData_0_1_0
      generatorPowerFamily_27_1_1 generatorPowerFamily_0_1_0

/-- The exact rational lower bound computed from the actual first rectangle data. -/
def firstGeneratorLeafLowerBound : ℚ :=
  rectangleIntervalLower firstGeneratorLeafIntervals (1 / 4) - firstGeneratorLeafError

/-- Ordinary Lean kernel computation proves the first exact interval lower bound positive. -/
theorem firstGeneratorLeafLowerBound_pos : 0 < firstGeneratorLeafLowerBound := by
  unfold firstGeneratorLeafLowerBound
  decide +kernel

end PartialBalayage.Maximal.Square
