/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorRectangleGeometry

/-!
# Actual rectangle literals for the generator subdivision

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Explicit dyadic rectangle labels, block 9. -/
def generatorPartitionRectangles9 : Fin 64 → GeneratorRectangle := ![
  ⟨19, 3, 3, 4, 7⟩,
  ⟨19, 3, 3, 4, 6⟩,
  ⟨19, 3, 3, 5, 5⟩,
  ⟨19, 3, 4, 11, 9⟩,
  ⟨19, 3, 4, 11, 8⟩,
  ⟨19, 3, 4, 10, 9⟩,
  ⟨19, 3, 4, 10, 8⟩,
  ⟨19, 3, 4, 9, 11⟩,
  ⟨19, 3, 4, 9, 10⟩,
  ⟨19, 3, 4, 8, 11⟩,
  ⟨19, 3, 4, 8, 10⟩,
  ⟨19, 3, 4, 9, 9⟩,
  ⟨19, 3, 4, 9, 8⟩,
  ⟨19, 3, 4, 8, 9⟩,
  ⟨19, 3, 4, 8, 8⟩,
  ⟨19, 3, 3, 7, 3⟩,
  ⟨19, 3, 3, 7, 2⟩,
  ⟨19, 3, 3, 6, 3⟩,
  ⟨19, 3, 3, 6, 2⟩,
  ⟨19, 3, 3, 7, 1⟩,
  ⟨19, 3, 3, 7, 0⟩,
  ⟨19, 3, 3, 6, 1⟩,
  ⟨19, 3, 3, 6, 0⟩,
  ⟨19, 3, 3, 5, 3⟩,
  ⟨19, 3, 3, 5, 2⟩,
  ⟨19, 3, 4, 9, 7⟩,
  ⟨19, 3, 4, 9, 6⟩,
  ⟨19, 3, 4, 8, 7⟩,
  ⟨19, 3, 4, 8, 6⟩,
  ⟨19, 3, 3, 4, 2⟩,
  ⟨19, 3, 3, 5, 1⟩,
  ⟨19, 3, 3, 5, 0⟩,
  ⟨19, 3, 3, 4, 1⟩,
  ⟨19, 3, 3, 4, 0⟩,
  ⟨19, 3, 3, 3, 7⟩,
  ⟨19, 3, 3, 3, 6⟩,
  ⟨19, 3, 3, 2, 7⟩,
  ⟨19, 3, 3, 2, 6⟩,
  ⟨19, 3, 3, 3, 5⟩,
  ⟨19, 3, 4, 7, 9⟩,
  ⟨19, 3, 4, 7, 8⟩,
  ⟨19, 3, 4, 6, 9⟩,
  ⟨19, 3, 4, 6, 8⟩,
  ⟨19, 3, 3, 2, 5⟩,
  ⟨19, 3, 3, 2, 4⟩,
  ⟨19, 3, 2, 0, 3⟩,
  ⟨19, 3, 3, 1, 5⟩,
  ⟨19, 3, 3, 1, 4⟩,
  ⟨19, 3, 3, 0, 5⟩,
  ⟨19, 3, 3, 0, 4⟩,
  ⟨19, 3, 4, 7, 7⟩,
  ⟨19, 3, 4, 7, 6⟩,
  ⟨19, 3, 4, 6, 7⟩,
  ⟨19, 3, 4, 6, 6⟩,
  ⟨19, 3, 3, 3, 2⟩,
  ⟨19, 3, 3, 2, 3⟩,
  ⟨19, 3, 3, 2, 2⟩,
  ⟨19, 3, 3, 3, 1⟩,
  ⟨19, 3, 3, 3, 0⟩,
  ⟨19, 3, 3, 2, 1⟩,
  ⟨19, 3, 3, 2, 0⟩,
  ⟨19, 3, 3, 1, 3⟩,
  ⟨19, 3, 3, 1, 2⟩,
  ⟨19, 3, 3, 0, 3⟩
]

end PartialBalayage.Maximal.Square
