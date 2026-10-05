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

/-- Explicit dyadic rectangle labels, block 7. -/
def generatorPartitionRectangles7 : Fin 64 → GeneratorRectangle := ![
  ⟨20, 2, 4, 6, 9⟩,
  ⟨20, 2, 4, 6, 8⟩,
  ⟨20, 2, 3, 2, 5⟩,
  ⟨20, 2, 3, 2, 4⟩,
  ⟨20, 2, 2, 0, 3⟩,
  ⟨20, 2, 3, 1, 5⟩,
  ⟨20, 2, 3, 1, 4⟩,
  ⟨20, 2, 3, 0, 5⟩,
  ⟨20, 2, 3, 0, 4⟩,
  ⟨20, 2, 4, 7, 7⟩,
  ⟨20, 2, 4, 7, 6⟩,
  ⟨20, 2, 4, 6, 7⟩,
  ⟨20, 2, 4, 6, 6⟩,
  ⟨20, 2, 3, 3, 2⟩,
  ⟨20, 2, 3, 2, 3⟩,
  ⟨20, 2, 3, 2, 2⟩,
  ⟨20, 2, 3, 3, 1⟩,
  ⟨20, 2, 3, 3, 0⟩,
  ⟨20, 2, 3, 2, 1⟩,
  ⟨20, 2, 3, 2, 0⟩,
  ⟨20, 2, 3, 1, 3⟩,
  ⟨20, 2, 3, 1, 2⟩,
  ⟨20, 2, 3, 0, 3⟩,
  ⟨20, 2, 3, 0, 2⟩,
  ⟨20, 2, 2, 0, 0⟩,
  ⟨20, 1, 2, 3, 3⟩,
  ⟨20, 1, 2, 3, 2⟩,
  ⟨20, 1, 2, 2, 3⟩,
  ⟨20, 1, 2, 2, 2⟩,
  ⟨20, 1, 2, 3, 1⟩,
  ⟨20, 1, 3, 7, 1⟩,
  ⟨20, 1, 3, 7, 0⟩,
  ⟨20, 1, 3, 6, 1⟩,
  ⟨20, 1, 3, 6, 0⟩,
  ⟨20, 1, 2, 2, 1⟩,
  ⟨20, 1, 2, 2, 0⟩,
  ⟨20, 1, 2, 1, 3⟩,
  ⟨20, 1, 2, 1, 2⟩,
  ⟨20, 1, 2, 0, 3⟩,
  ⟨20, 1, 2, 0, 2⟩,
  ⟨20, 1, 2, 1, 1⟩,
  ⟨20, 1, 2, 1, 0⟩,
  ⟨20, 1, 2, 0, 1⟩,
  ⟨20, 1, 2, 0, 0⟩,
  ⟨20, 0, 3, 7, 7⟩,
  ⟨20, 0, 3, 7, 6⟩,
  ⟨20, 0, 3, 6, 7⟩,
  ⟨20, 0, 3, 6, 6⟩,
  ⟨20, 0, 2, 3, 2⟩,
  ⟨20, 0, 3, 5, 7⟩,
  ⟨20, 0, 3, 5, 6⟩,
  ⟨20, 0, 3, 4, 7⟩,
  ⟨20, 0, 3, 4, 6⟩,
  ⟨20, 0, 2, 2, 2⟩,
  ⟨20, 0, 2, 3, 1⟩,
  ⟨20, 0, 2, 3, 0⟩,
  ⟨20, 0, 2, 2, 1⟩,
  ⟨20, 0, 2, 2, 0⟩,
  ⟨20, 0, 3, 3, 7⟩,
  ⟨20, 0, 3, 3, 6⟩,
  ⟨20, 0, 3, 2, 7⟩,
  ⟨20, 0, 3, 2, 6⟩,
  ⟨20, 0, 2, 1, 2⟩,
  ⟨20, 0, 3, 1, 7⟩
]

end PartialBalayage.Maximal.Square
