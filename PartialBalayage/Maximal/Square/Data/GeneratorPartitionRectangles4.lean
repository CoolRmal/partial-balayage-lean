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

/-- Explicit dyadic rectangle labels, block 4. -/
def generatorPartitionRectangles4 : Fin 64 → GeneratorRectangle := ![
  ⟨21, 2, 3, 0, 3⟩,
  ⟨21, 2, 3, 0, 2⟩,
  ⟨21, 2, 3, 1, 1⟩,
  ⟨21, 2, 3, 1, 0⟩,
  ⟨21, 2, 3, 0, 1⟩,
  ⟨21, 2, 3, 0, 0⟩,
  ⟨21, 1, 3, 7, 7⟩,
  ⟨21, 1, 3, 7, 6⟩,
  ⟨21, 1, 3, 6, 7⟩,
  ⟨21, 1, 3, 6, 6⟩,
  ⟨21, 1, 3, 7, 5⟩,
  ⟨21, 1, 3, 7, 4⟩,
  ⟨21, 1, 3, 6, 5⟩,
  ⟨21, 1, 3, 6, 4⟩,
  ⟨21, 1, 3, 5, 7⟩,
  ⟨21, 1, 3, 5, 6⟩,
  ⟨21, 1, 3, 4, 7⟩,
  ⟨21, 1, 3, 4, 6⟩,
  ⟨21, 1, 4, 11, 11⟩,
  ⟨21, 1, 4, 11, 10⟩,
  ⟨21, 1, 4, 10, 11⟩,
  ⟨21, 1, 4, 10, 10⟩,
  ⟨21, 1, 4, 11, 9⟩,
  ⟨21, 1, 4, 11, 8⟩,
  ⟨21, 1, 4, 10, 9⟩,
  ⟨21, 1, 4, 10, 8⟩,
  ⟨21, 1, 4, 9, 11⟩,
  ⟨21, 1, 4, 9, 10⟩,
  ⟨21, 1, 4, 8, 11⟩,
  ⟨21, 1, 4, 8, 10⟩,
  ⟨21, 1, 4, 9, 9⟩,
  ⟨21, 1, 4, 9, 8⟩,
  ⟨21, 1, 4, 8, 9⟩,
  ⟨21, 1, 4, 8, 8⟩,
  ⟨21, 1, 3, 7, 3⟩,
  ⟨21, 1, 3, 7, 2⟩,
  ⟨21, 1, 3, 6, 3⟩,
  ⟨21, 1, 3, 6, 2⟩,
  ⟨21, 1, 2, 3, 0⟩,
  ⟨21, 1, 3, 5, 3⟩,
  ⟨21, 1, 3, 5, 2⟩,
  ⟨21, 1, 4, 9, 7⟩,
  ⟨21, 1, 4, 9, 6⟩,
  ⟨21, 1, 4, 8, 7⟩,
  ⟨21, 1, 4, 8, 6⟩,
  ⟨21, 1, 3, 4, 2⟩,
  ⟨21, 1, 3, 5, 1⟩,
  ⟨21, 1, 3, 5, 0⟩,
  ⟨21, 1, 3, 4, 1⟩,
  ⟨21, 1, 3, 4, 0⟩,
  ⟨21, 1, 3, 3, 7⟩,
  ⟨21, 1, 3, 3, 6⟩,
  ⟨21, 1, 3, 2, 7⟩,
  ⟨21, 1, 3, 2, 6⟩,
  ⟨21, 1, 3, 3, 5⟩,
  ⟨21, 1, 4, 7, 9⟩,
  ⟨21, 1, 4, 7, 8⟩,
  ⟨21, 1, 4, 6, 9⟩,
  ⟨21, 1, 4, 6, 8⟩,
  ⟨21, 1, 3, 2, 5⟩,
  ⟨21, 1, 3, 2, 4⟩,
  ⟨21, 1, 2, 0, 3⟩,
  ⟨21, 1, 3, 1, 5⟩,
  ⟨21, 1, 3, 1, 4⟩
]

end PartialBalayage.Maximal.Square
