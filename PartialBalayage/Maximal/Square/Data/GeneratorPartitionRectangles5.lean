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

/-- Explicit dyadic rectangle labels, block 5. -/
def generatorPartitionRectangles5 : Fin 64 → GeneratorRectangle := ![
  ⟨21, 1, 3, 0, 5⟩,
  ⟨21, 1, 3, 0, 4⟩,
  ⟨21, 1, 4, 7, 7⟩,
  ⟨21, 1, 4, 7, 6⟩,
  ⟨21, 1, 4, 6, 7⟩,
  ⟨21, 1, 4, 6, 6⟩,
  ⟨21, 1, 3, 3, 2⟩,
  ⟨21, 1, 3, 2, 3⟩,
  ⟨21, 1, 3, 2, 2⟩,
  ⟨21, 1, 3, 3, 1⟩,
  ⟨21, 1, 3, 3, 0⟩,
  ⟨21, 1, 3, 2, 1⟩,
  ⟨21, 1, 3, 2, 0⟩,
  ⟨21, 1, 2, 0, 1⟩,
  ⟨21, 1, 2, 0, 0⟩,
  ⟨21, 0, 2, 3, 3⟩,
  ⟨21, 0, 2, 3, 2⟩,
  ⟨21, 0, 2, 2, 3⟩,
  ⟨21, 0, 2, 2, 2⟩,
  ⟨21, 0, 3, 7, 3⟩,
  ⟨21, 0, 3, 7, 2⟩,
  ⟨21, 0, 3, 6, 3⟩,
  ⟨21, 0, 3, 6, 2⟩,
  ⟨21, 0, 3, 7, 1⟩,
  ⟨21, 0, 3, 7, 0⟩,
  ⟨21, 0, 3, 6, 1⟩,
  ⟨21, 0, 3, 6, 0⟩,
  ⟨21, 0, 2, 2, 1⟩,
  ⟨21, 0, 3, 5, 1⟩,
  ⟨21, 0, 3, 5, 0⟩,
  ⟨21, 0, 3, 4, 1⟩,
  ⟨21, 0, 3, 4, 0⟩,
  ⟨21, 0, 2, 1, 3⟩,
  ⟨21, 0, 2, 1, 2⟩,
  ⟨21, 0, 3, 1, 7⟩,
  ⟨21, 0, 3, 1, 6⟩,
  ⟨21, 0, 3, 0, 7⟩,
  ⟨21, 0, 3, 0, 6⟩,
  ⟨21, 0, 2, 0, 2⟩,
  ⟨21, 0, 2, 1, 1⟩,
  ⟨21, 0, 3, 3, 1⟩,
  ⟨21, 0, 3, 3, 0⟩,
  ⟨21, 0, 3, 2, 1⟩,
  ⟨21, 0, 3, 2, 0⟩,
  ⟨21, 0, 2, 0, 1⟩,
  ⟨21, 0, 2, 0, 0⟩,
  ⟨20, 7, 1, 1, 0⟩,
  ⟨20, 7, 1, 0, 1⟩,
  ⟨20, 7, 1, 0, 0⟩,
  ⟨20, 6, 0, 0, 0⟩,
  ⟨20, 5, 1, 1, 1⟩,
  ⟨20, 5, 1, 1, 0⟩,
  ⟨20, 5, 1, 0, 1⟩,
  ⟨20, 5, 1, 0, 0⟩,
  ⟨20, 4, 1, 1, 1⟩,
  ⟨20, 4, 1, 1, 0⟩,
  ⟨20, 4, 1, 0, 1⟩,
  ⟨20, 4, 1, 0, 0⟩,
  ⟨20, 3, 1, 1, 1⟩,
  ⟨20, 3, 2, 3, 1⟩,
  ⟨20, 3, 2, 3, 0⟩,
  ⟨20, 3, 2, 2, 1⟩,
  ⟨20, 3, 2, 2, 0⟩,
  ⟨20, 3, 2, 1, 3⟩
]

end PartialBalayage.Maximal.Square
