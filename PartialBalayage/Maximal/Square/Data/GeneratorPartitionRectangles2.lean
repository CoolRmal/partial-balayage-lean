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

/-- Explicit dyadic rectangle labels, block 2. -/
def generatorPartitionRectangles2 : Fin 64 → GeneratorRectangle := ![
  ⟨22, 1, 3, 4, 0⟩,
  ⟨22, 1, 2, 1, 3⟩,
  ⟨22, 1, 2, 1, 2⟩,
  ⟨22, 1, 2, 0, 3⟩,
  ⟨22, 1, 3, 1, 5⟩,
  ⟨22, 1, 3, 1, 4⟩,
  ⟨22, 1, 3, 0, 5⟩,
  ⟨22, 1, 3, 0, 4⟩,
  ⟨22, 1, 2, 1, 1⟩,
  ⟨22, 1, 3, 3, 1⟩,
  ⟨22, 1, 3, 3, 0⟩,
  ⟨22, 1, 3, 2, 1⟩,
  ⟨22, 1, 3, 2, 0⟩,
  ⟨22, 1, 3, 1, 3⟩,
  ⟨22, 1, 3, 1, 2⟩,
  ⟨22, 1, 3, 0, 3⟩,
  ⟨22, 1, 3, 0, 2⟩,
  ⟨22, 1, 2, 0, 0⟩,
  ⟨22, 0, 3, 7, 7⟩,
  ⟨22, 0, 3, 7, 6⟩,
  ⟨22, 0, 3, 6, 7⟩,
  ⟨22, 0, 3, 6, 6⟩,
  ⟨22, 0, 3, 7, 5⟩,
  ⟨22, 0, 3, 7, 4⟩,
  ⟨22, 0, 3, 6, 5⟩,
  ⟨22, 0, 3, 6, 4⟩,
  ⟨22, 0, 3, 5, 7⟩,
  ⟨22, 0, 4, 11, 13⟩,
  ⟨22, 0, 4, 11, 12⟩,
  ⟨22, 0, 4, 10, 13⟩,
  ⟨22, 0, 4, 10, 12⟩,
  ⟨22, 0, 3, 4, 7⟩,
  ⟨22, 0, 4, 9, 13⟩,
  ⟨22, 0, 4, 9, 12⟩,
  ⟨22, 0, 4, 8, 13⟩,
  ⟨22, 0, 4, 8, 12⟩,
  ⟨22, 0, 4, 11, 11⟩,
  ⟨22, 0, 4, 11, 10⟩,
  ⟨22, 0, 4, 10, 11⟩,
  ⟨22, 0, 4, 10, 10⟩,
  ⟨22, 0, 3, 5, 4⟩,
  ⟨22, 0, 4, 9, 11⟩,
  ⟨22, 0, 4, 9, 10⟩,
  ⟨22, 0, 4, 8, 11⟩,
  ⟨22, 0, 4, 8, 10⟩,
  ⟨22, 0, 4, 9, 9⟩,
  ⟨22, 0, 4, 9, 8⟩,
  ⟨22, 0, 4, 8, 9⟩,
  ⟨22, 0, 4, 8, 8⟩,
  ⟨22, 0, 2, 3, 1⟩,
  ⟨22, 0, 2, 3, 0⟩,
  ⟨22, 0, 3, 5, 3⟩,
  ⟨22, 0, 3, 5, 2⟩,
  ⟨22, 0, 3, 4, 3⟩,
  ⟨22, 0, 3, 4, 2⟩,
  ⟨22, 0, 2, 2, 0⟩,
  ⟨22, 0, 3, 3, 7⟩,
  ⟨22, 0, 4, 7, 13⟩,
  ⟨22, 0, 4, 7, 12⟩,
  ⟨22, 0, 4, 6, 13⟩,
  ⟨22, 0, 4, 6, 12⟩,
  ⟨22, 0, 3, 2, 7⟩,
  ⟨22, 0, 3, 2, 6⟩,
  ⟨22, 0, 4, 7, 11⟩
]

end PartialBalayage.Maximal.Square
