/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates0
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates1
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 74 of the recorded finite partition. -/
def generatorLeafBlocks74 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 74 0
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 74 1
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 74 2
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 74 3
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 74 4
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 74 5
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 74 6
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 74 7
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 74 8
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 74 9
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 74 10
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 74 11
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 74 12
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 74 13
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 14
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 15
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 74 16
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 74 17
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 18
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 19
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 74 20
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 74 21
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 74 22
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 74 23
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 74 24
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 74 25
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 74 26
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 74 27
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 74 28
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 74 29
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 30
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 31
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 74 32
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 74 33
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 34
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 74 35
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 74 36
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 74 37
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 74 38
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 74 39
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 74 40
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 74 41
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 74 42
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 74 43
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 74 44
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 74 45
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 74 46
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 74 47
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 74 48
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 74 49
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 74 50
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 74 51
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 74 52
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 74 53
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 74 54
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 74 55
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 74 56
    coordinateU := generatorCoordinates29 1
    coordinateV := generatorCoordinates29 1
    terms := 4
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 74 57
    coordinateU := generatorCoordinates29 1
    coordinateV := generatorCoordinates29 0
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 74 58
    coordinateU := generatorCoordinates29 0
    coordinateV := generatorCoordinates29 1
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 74 59
    coordinateU := generatorCoordinates29 0
    coordinateV := generatorCoordinates29 0
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 74 60
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates25 6
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 74 61
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 74 62
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates25 6
    terms := 4
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 74 63
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates25 5
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks74_valid : ∀ i, (generatorLeafBlocks74 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks74 i).coordinateU.IsValid ∧
      (generatorLeafBlocks74 i).coordinateV.IsValid ∧
      (generatorLeafBlocks74 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates29_valid 1,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates29_valid 1,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates29_valid 0,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates29_valid 0,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 2 61⟩
  have hMeta : ∀ i, (generatorLeafBlocks74 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks74 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
