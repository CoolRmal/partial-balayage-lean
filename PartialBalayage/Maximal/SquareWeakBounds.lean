/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SquarePositiveSource
public import PartialBalayage.Maximal.Square.SquareWeakBoundOfSourcePositivity

/-!
# The strict square maximal bound

The actual comparison kernel, positive generator source, stable obstacle,
and all-input transfer give the table's exact strict bound for centered squares.
-/

@[expose] public section

namespace PartialBalayage.Maximal

/-- The centered square maximal operator has weak-type constant strictly below 3.616. -/
theorem square_weakTypeConstant_lt_3_616 :
    cubeWeakTypeConstant 2 < ENNReal.ofReal (452 / 125 : ℝ) :=
  Square.cubeWeakTypeConstant_lt_of_square_source_nonneg
    Square.ae_squareGeneratorDensity_nonneg

end PartialBalayage.Maximal
