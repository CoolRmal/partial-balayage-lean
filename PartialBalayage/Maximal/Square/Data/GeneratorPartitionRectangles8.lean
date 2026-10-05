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

/-- Explicit dyadic rectangle labels, block 8. -/
def generatorPartitionRectangles8 : Fin 64 → GeneratorRectangle := ![
  ⟨20, 0, 3, 1, 6⟩,
  ⟨20, 0, 3, 0, 7⟩,
  ⟨20, 0, 3, 0, 6⟩,
  ⟨20, 0, 2, 0, 2⟩,
  ⟨20, 0, 3, 3, 3⟩,
  ⟨20, 0, 3, 3, 2⟩,
  ⟨20, 0, 3, 2, 3⟩,
  ⟨20, 0, 3, 2, 2⟩,
  ⟨20, 0, 2, 1, 0⟩,
  ⟨20, 0, 3, 1, 3⟩,
  ⟨20, 0, 3, 1, 2⟩,
  ⟨20, 0, 3, 0, 3⟩,
  ⟨20, 0, 3, 0, 2⟩,
  ⟨20, 0, 2, 0, 0⟩,
  ⟨19, 8, 1, 1, 0⟩,
  ⟨19, 8, 1, 0, 1⟩,
  ⟨19, 8, 1, 0, 0⟩,
  ⟨19, 7, 0, 0, 0⟩,
  ⟨19, 6, 1, 1, 1⟩,
  ⟨19, 6, 1, 1, 0⟩,
  ⟨19, 6, 1, 0, 1⟩,
  ⟨19, 6, 1, 0, 0⟩,
  ⟨19, 5, 1, 1, 1⟩,
  ⟨19, 5, 1, 1, 0⟩,
  ⟨19, 5, 1, 0, 1⟩,
  ⟨19, 5, 2, 1, 1⟩,
  ⟨19, 5, 2, 1, 0⟩,
  ⟨19, 5, 2, 0, 1⟩,
  ⟨19, 5, 2, 0, 0⟩,
  ⟨19, 4, 1, 1, 1⟩,
  ⟨19, 4, 2, 3, 1⟩,
  ⟨19, 4, 2, 3, 0⟩,
  ⟨19, 4, 2, 2, 1⟩,
  ⟨19, 4, 2, 2, 0⟩,
  ⟨19, 4, 2, 1, 3⟩,
  ⟨19, 4, 2, 1, 2⟩,
  ⟨19, 4, 2, 0, 3⟩,
  ⟨19, 4, 3, 1, 5⟩,
  ⟨19, 4, 3, 1, 4⟩,
  ⟨19, 4, 3, 0, 5⟩,
  ⟨19, 4, 3, 0, 4⟩,
  ⟨19, 4, 2, 1, 1⟩,
  ⟨19, 4, 3, 3, 1⟩,
  ⟨19, 4, 3, 3, 0⟩,
  ⟨19, 4, 3, 2, 1⟩,
  ⟨19, 4, 3, 2, 0⟩,
  ⟨19, 4, 3, 1, 3⟩,
  ⟨19, 4, 3, 1, 2⟩,
  ⟨19, 4, 3, 0, 3⟩,
  ⟨19, 4, 3, 0, 2⟩,
  ⟨19, 4, 3, 1, 1⟩,
  ⟨19, 4, 3, 1, 0⟩,
  ⟨19, 4, 3, 0, 1⟩,
  ⟨19, 4, 3, 0, 0⟩,
  ⟨19, 3, 3, 7, 7⟩,
  ⟨19, 3, 3, 7, 6⟩,
  ⟨19, 3, 3, 6, 7⟩,
  ⟨19, 3, 3, 6, 6⟩,
  ⟨19, 3, 3, 7, 5⟩,
  ⟨19, 3, 3, 7, 4⟩,
  ⟨19, 3, 3, 6, 5⟩,
  ⟨19, 3, 3, 6, 4⟩,
  ⟨19, 3, 3, 5, 7⟩,
  ⟨19, 3, 3, 5, 6⟩
]

end PartialBalayage.Maximal.Square
