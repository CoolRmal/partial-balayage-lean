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

/-- Explicit dyadic rectangle labels, block 0. -/
def generatorPartitionRectangles0 : Fin 64 → GeneratorRectangle := ![
  ⟨27, 0, 1, 1, 0⟩,
  ⟨27, 0, 1, 0, 1⟩,
  ⟨27, 0, 1, 0, 0⟩,
  ⟨26, 1, 1, 1, 0⟩,
  ⟨26, 1, 1, 0, 1⟩,
  ⟨26, 1, 1, 0, 0⟩,
  ⟨26, 0, 0, 0, 0⟩,
  ⟨25, 2, 1, 1, 0⟩,
  ⟨25, 2, 1, 0, 1⟩,
  ⟨25, 2, 1, 0, 0⟩,
  ⟨25, 1, 0, 0, 0⟩,
  ⟨25, 0, 0, 0, 0⟩,
  ⟨24, 3, 1, 1, 0⟩,
  ⟨24, 3, 1, 0, 1⟩,
  ⟨24, 3, 1, 0, 0⟩,
  ⟨24, 2, 0, 0, 0⟩,
  ⟨24, 1, 1, 1, 1⟩,
  ⟨24, 1, 1, 1, 0⟩,
  ⟨24, 1, 1, 0, 1⟩,
  ⟨24, 1, 1, 0, 0⟩,
  ⟨24, 0, 1, 1, 1⟩,
  ⟨24, 0, 1, 1, 0⟩,
  ⟨24, 0, 1, 0, 1⟩,
  ⟨24, 0, 2, 1, 1⟩,
  ⟨24, 0, 2, 1, 0⟩,
  ⟨24, 0, 2, 0, 1⟩,
  ⟨24, 0, 3, 1, 1⟩,
  ⟨24, 0, 3, 1, 0⟩,
  ⟨24, 0, 3, 0, 1⟩,
  ⟨24, 0, 3, 0, 0⟩,
  ⟨23, 4, 1, 1, 0⟩,
  ⟨23, 4, 1, 0, 1⟩,
  ⟨23, 4, 1, 0, 0⟩,
  ⟨23, 3, 0, 0, 0⟩,
  ⟨23, 2, 1, 1, 1⟩,
  ⟨23, 2, 1, 1, 0⟩,
  ⟨23, 2, 1, 0, 1⟩,
  ⟨23, 2, 1, 0, 0⟩,
  ⟨23, 1, 1, 1, 1⟩,
  ⟨23, 1, 1, 1, 0⟩,
  ⟨23, 1, 1, 0, 1⟩,
  ⟨23, 1, 2, 1, 1⟩,
  ⟨23, 1, 2, 1, 0⟩,
  ⟨23, 1, 2, 0, 1⟩,
  ⟨23, 1, 2, 0, 0⟩,
  ⟨23, 0, 2, 3, 3⟩,
  ⟨23, 0, 2, 3, 2⟩,
  ⟨23, 0, 2, 2, 3⟩,
  ⟨23, 0, 2, 2, 2⟩,
  ⟨23, 0, 2, 3, 1⟩,
  ⟨23, 0, 3, 7, 1⟩,
  ⟨23, 0, 4, 15, 1⟩,
  ⟨23, 0, 4, 15, 0⟩,
  ⟨23, 0, 4, 14, 1⟩,
  ⟨23, 0, 4, 14, 0⟩,
  ⟨23, 0, 3, 6, 1⟩,
  ⟨23, 0, 4, 13, 1⟩,
  ⟨23, 0, 4, 13, 0⟩,
  ⟨23, 0, 4, 12, 1⟩,
  ⟨23, 0, 5, 25, 1⟩,
  ⟨23, 0, 5, 25, 0⟩,
  ⟨23, 0, 5, 24, 1⟩,
  ⟨23, 0, 5, 24, 0⟩,
  ⟨23, 0, 2, 2, 1⟩
]

end PartialBalayage.Maximal.Square
