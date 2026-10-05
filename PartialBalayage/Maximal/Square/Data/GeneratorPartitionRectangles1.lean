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

/-- Explicit dyadic rectangle labels, block 1. -/
def generatorPartitionRectangles1 : Fin 64 → GeneratorRectangle := ![
  ⟨23, 0, 3, 5, 1⟩,
  ⟨23, 0, 4, 11, 1⟩,
  ⟨23, 0, 5, 23, 1⟩,
  ⟨23, 0, 5, 23, 0⟩,
  ⟨23, 0, 5, 22, 1⟩,
  ⟨23, 0, 5, 22, 0⟩,
  ⟨23, 0, 4, 10, 1⟩,
  ⟨23, 0, 5, 21, 1⟩,
  ⟨23, 0, 5, 21, 0⟩,
  ⟨23, 0, 5, 20, 1⟩,
  ⟨23, 0, 5, 20, 0⟩,
  ⟨23, 0, 3, 4, 1⟩,
  ⟨23, 0, 4, 9, 1⟩,
  ⟨23, 0, 5, 19, 1⟩,
  ⟨23, 0, 5, 19, 0⟩,
  ⟨23, 0, 5, 18, 1⟩,
  ⟨23, 0, 5, 18, 0⟩,
  ⟨23, 0, 4, 8, 1⟩,
  ⟨23, 0, 4, 8, 0⟩,
  ⟨23, 0, 2, 1, 3⟩,
  ⟨23, 0, 2, 1, 2⟩,
  ⟨23, 0, 3, 1, 7⟩,
  ⟨23, 0, 3, 1, 6⟩,
  ⟨23, 0, 3, 0, 7⟩,
  ⟨23, 0, 3, 0, 6⟩,
  ⟨23, 0, 3, 1, 5⟩,
  ⟨23, 0, 3, 1, 4⟩,
  ⟨23, 0, 3, 0, 5⟩,
  ⟨23, 0, 3, 0, 4⟩,
  ⟨23, 0, 2, 1, 1⟩,
  ⟨23, 0, 3, 3, 1⟩,
  ⟨23, 0, 4, 7, 1⟩,
  ⟨23, 0, 4, 7, 0⟩,
  ⟨23, 0, 4, 6, 1⟩,
  ⟨23, 0, 4, 6, 0⟩,
  ⟨23, 0, 3, 2, 1⟩,
  ⟨23, 0, 3, 2, 0⟩,
  ⟨23, 0, 2, 0, 1⟩,
  ⟨23, 0, 2, 0, 0⟩,
  ⟨22, 5, 1, 1, 0⟩,
  ⟨22, 5, 1, 0, 1⟩,
  ⟨22, 5, 1, 0, 0⟩,
  ⟨22, 4, 0, 0, 0⟩,
  ⟨22, 3, 1, 1, 1⟩,
  ⟨22, 3, 1, 1, 0⟩,
  ⟨22, 3, 1, 0, 1⟩,
  ⟨22, 3, 1, 0, 0⟩,
  ⟨22, 2, 1, 1, 1⟩,
  ⟨22, 2, 1, 1, 0⟩,
  ⟨22, 2, 1, 0, 1⟩,
  ⟨22, 2, 2, 1, 1⟩,
  ⟨22, 2, 2, 1, 0⟩,
  ⟨22, 2, 2, 0, 1⟩,
  ⟨22, 2, 2, 0, 0⟩,
  ⟨22, 1, 1, 1, 1⟩,
  ⟨22, 1, 2, 3, 1⟩,
  ⟨22, 1, 3, 7, 1⟩,
  ⟨22, 1, 3, 7, 0⟩,
  ⟨22, 1, 3, 6, 1⟩,
  ⟨22, 1, 3, 6, 0⟩,
  ⟨22, 1, 2, 2, 1⟩,
  ⟨22, 1, 3, 5, 1⟩,
  ⟨22, 1, 3, 5, 0⟩,
  ⟨22, 1, 3, 4, 1⟩
]

end PartialBalayage.Maximal.Square
