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

/-- Explicit dyadic rectangle labels, block 3. -/
def generatorPartitionRectangles3 : Fin 64 → GeneratorRectangle := ![
  ⟨22, 0, 4, 7, 10⟩,
  ⟨22, 0, 4, 6, 11⟩,
  ⟨22, 0, 4, 6, 10⟩,
  ⟨22, 0, 3, 3, 4⟩,
  ⟨22, 0, 3, 2, 5⟩,
  ⟨22, 0, 3, 2, 4⟩,
  ⟨22, 0, 3, 1, 7⟩,
  ⟨22, 0, 3, 1, 6⟩,
  ⟨22, 0, 3, 0, 7⟩,
  ⟨22, 0, 3, 0, 6⟩,
  ⟨22, 0, 3, 1, 5⟩,
  ⟨22, 0, 3, 1, 4⟩,
  ⟨22, 0, 3, 0, 5⟩,
  ⟨22, 0, 3, 0, 4⟩,
  ⟨22, 0, 3, 3, 3⟩,
  ⟨22, 0, 3, 3, 2⟩,
  ⟨22, 0, 3, 2, 3⟩,
  ⟨22, 0, 3, 2, 2⟩,
  ⟨22, 0, 3, 3, 1⟩,
  ⟨22, 0, 3, 3, 0⟩,
  ⟨22, 0, 3, 2, 1⟩,
  ⟨22, 0, 3, 2, 0⟩,
  ⟨22, 0, 2, 0, 1⟩,
  ⟨22, 0, 3, 1, 1⟩,
  ⟨22, 0, 3, 1, 0⟩,
  ⟨22, 0, 3, 0, 1⟩,
  ⟨22, 0, 3, 0, 0⟩,
  ⟨21, 6, 1, 1, 0⟩,
  ⟨21, 6, 1, 0, 1⟩,
  ⟨21, 6, 1, 0, 0⟩,
  ⟨21, 5, 0, 0, 0⟩,
  ⟨21, 4, 1, 1, 1⟩,
  ⟨21, 4, 1, 1, 0⟩,
  ⟨21, 4, 1, 0, 1⟩,
  ⟨21, 4, 1, 0, 0⟩,
  ⟨21, 3, 1, 1, 1⟩,
  ⟨21, 3, 1, 1, 0⟩,
  ⟨21, 3, 1, 0, 1⟩,
  ⟨21, 3, 2, 1, 1⟩,
  ⟨21, 3, 2, 1, 0⟩,
  ⟨21, 3, 2, 0, 1⟩,
  ⟨21, 3, 2, 0, 0⟩,
  ⟨21, 2, 1, 1, 1⟩,
  ⟨21, 2, 2, 3, 1⟩,
  ⟨21, 2, 2, 3, 0⟩,
  ⟨21, 2, 2, 2, 1⟩,
  ⟨21, 2, 3, 5, 1⟩,
  ⟨21, 2, 3, 5, 0⟩,
  ⟨21, 2, 3, 4, 1⟩,
  ⟨21, 2, 3, 4, 0⟩,
  ⟨21, 2, 2, 1, 3⟩,
  ⟨21, 2, 2, 1, 2⟩,
  ⟨21, 2, 2, 0, 3⟩,
  ⟨21, 2, 3, 1, 5⟩,
  ⟨21, 2, 3, 1, 4⟩,
  ⟨21, 2, 3, 0, 5⟩,
  ⟨21, 2, 3, 0, 4⟩,
  ⟨21, 2, 2, 1, 1⟩,
  ⟨21, 2, 3, 3, 1⟩,
  ⟨21, 2, 3, 3, 0⟩,
  ⟨21, 2, 3, 2, 1⟩,
  ⟨21, 2, 3, 2, 0⟩,
  ⟨21, 2, 3, 1, 3⟩,
  ⟨21, 2, 3, 1, 2⟩
]

end PartialBalayage.Maximal.Square
