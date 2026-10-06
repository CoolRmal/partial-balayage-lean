/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 42 of the recorded finite partition. -/
def generatorLeafBlocks42 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 42 0
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 42 1
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 42 2
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 42 3
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 42 4
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 42 5
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 42 6
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 42 7
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates29 5
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 42 8
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates29 4
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 42 9
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 42 10
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 42 11
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 42 12
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 42 13
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 42 14
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 42 15
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 42 16
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 42 17
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates29 3
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 42 18
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates29 2
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 42 19
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates29 5
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 42 20
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates29 4
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 42 21
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 42 22
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 42 23
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates32 5
    terms := 12
    radialRoot := generatorRadialRoots 3 62
  },
  {
    rectangle := generatorPartitionRectangles 42 24
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates32 4
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 42 25
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates32 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 42 26
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates32 4
    terms := 12
    radialRoot := generatorRadialRoots 3 60
  },
  {
    rectangle := generatorPartitionRectangles 42 27
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 42 28
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 42 29
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 42 30
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates30 3
    terms := 20
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 42 31
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates30 2
    terms := 20
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 42 32
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates29 3
    terms := 8
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 42 33
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates29 2
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 42 34
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 42 35
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 42 36
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates30 1
    terms := 20
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 42 37
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 42 38
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 42 39
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 42 40
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 42 41
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 42 42
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 42 43
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 42 44
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 42 45
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 42 46
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 42 47
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 42 48
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 42 49
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 42 50
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 42 51
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 42 52
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 42 53
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 42 54
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 42 55
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 42 56
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 42 57
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 42 58
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 42 59
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 42 60
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 42 61
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 42 62
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 42 63
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 3 46
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks42_valid : ∀ i, (generatorLeafBlocks42 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks42 i).coordinateU.IsValid ∧
      (generatorLeafBlocks42 i).coordinateV.IsValid ∧
      (generatorLeafBlocks42 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates32_valid 5, generatorRadialRoots_valid 3 62⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates32_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates32_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates32_valid 4, generatorRadialRoots_valid 3 60⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 46⟩
  have hMeta : ∀ i, (generatorLeafBlocks42 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks42 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
