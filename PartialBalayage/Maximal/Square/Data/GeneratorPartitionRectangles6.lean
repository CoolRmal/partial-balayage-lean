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

/-- Explicit dyadic rectangle labels, block 6. -/
def generatorPartitionRectangles6 : Fin 64 → GeneratorRectangle := ![
  ⟨20, 3, 2, 1, 2⟩,
  ⟨20, 3, 2, 0, 3⟩,
  ⟨20, 3, 2, 0, 2⟩,
  ⟨20, 3, 2, 1, 1⟩,
  ⟨20, 3, 3, 3, 1⟩,
  ⟨20, 3, 3, 3, 0⟩,
  ⟨20, 3, 3, 2, 1⟩,
  ⟨20, 3, 3, 2, 0⟩,
  ⟨20, 3, 3, 1, 3⟩,
  ⟨20, 3, 3, 1, 2⟩,
  ⟨20, 3, 3, 0, 3⟩,
  ⟨20, 3, 3, 0, 2⟩,
  ⟨20, 3, 3, 1, 1⟩,
  ⟨20, 3, 3, 1, 0⟩,
  ⟨20, 3, 3, 0, 1⟩,
  ⟨20, 3, 3, 0, 0⟩,
  ⟨20, 2, 3, 7, 7⟩,
  ⟨20, 2, 3, 7, 6⟩,
  ⟨20, 2, 3, 6, 7⟩,
  ⟨20, 2, 3, 6, 6⟩,
  ⟨20, 2, 3, 7, 5⟩,
  ⟨20, 2, 3, 7, 4⟩,
  ⟨20, 2, 3, 6, 5⟩,
  ⟨20, 2, 3, 6, 4⟩,
  ⟨20, 2, 3, 5, 7⟩,
  ⟨20, 2, 3, 5, 6⟩,
  ⟨20, 2, 3, 4, 7⟩,
  ⟨20, 2, 3, 4, 6⟩,
  ⟨20, 2, 3, 5, 5⟩,
  ⟨20, 2, 4, 11, 9⟩,
  ⟨20, 2, 4, 11, 8⟩,
  ⟨20, 2, 4, 10, 9⟩,
  ⟨20, 2, 4, 10, 8⟩,
  ⟨20, 2, 4, 9, 11⟩,
  ⟨20, 2, 4, 9, 10⟩,
  ⟨20, 2, 4, 8, 11⟩,
  ⟨20, 2, 4, 8, 10⟩,
  ⟨20, 2, 4, 9, 9⟩,
  ⟨20, 2, 4, 9, 8⟩,
  ⟨20, 2, 4, 8, 9⟩,
  ⟨20, 2, 4, 8, 8⟩,
  ⟨20, 2, 3, 7, 3⟩,
  ⟨20, 2, 3, 7, 2⟩,
  ⟨20, 2, 3, 6, 3⟩,
  ⟨20, 2, 3, 6, 2⟩,
  ⟨20, 2, 2, 3, 0⟩,
  ⟨20, 2, 3, 5, 3⟩,
  ⟨20, 2, 3, 5, 2⟩,
  ⟨20, 2, 4, 9, 7⟩,
  ⟨20, 2, 4, 9, 6⟩,
  ⟨20, 2, 4, 8, 7⟩,
  ⟨20, 2, 4, 8, 6⟩,
  ⟨20, 2, 3, 4, 2⟩,
  ⟨20, 2, 3, 5, 1⟩,
  ⟨20, 2, 3, 5, 0⟩,
  ⟨20, 2, 3, 4, 1⟩,
  ⟨20, 2, 3, 4, 0⟩,
  ⟨20, 2, 3, 3, 7⟩,
  ⟨20, 2, 3, 3, 6⟩,
  ⟨20, 2, 3, 2, 7⟩,
  ⟨20, 2, 3, 2, 6⟩,
  ⟨20, 2, 3, 3, 5⟩,
  ⟨20, 2, 4, 7, 9⟩,
  ⟨20, 2, 4, 7, 8⟩
]

end PartialBalayage.Maximal.Square
