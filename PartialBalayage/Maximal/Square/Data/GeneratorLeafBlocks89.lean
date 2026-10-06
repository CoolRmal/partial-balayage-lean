/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates16
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates24

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 89 of the recorded finite partition. -/
def generatorLeafBlocks89 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 89 0
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 89 1
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 89 2
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates15 3
    terms := 1
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 89 3
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates15 2
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 89 4
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 7
    terms := 1
    radialRoot := generatorRadialRoots 1 62
  },
  {
    rectangle := generatorPartitionRectangles 89 5
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 6
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 89 6
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 7
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 89 7
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 6
    terms := 2
    radialRoot := generatorRadialRoots 1 60
  },
  {
    rectangle := generatorPartitionRectangles 89 8
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 5
    terms := 2
    radialRoot := generatorRadialRoots 1 60
  },
  {
    rectangle := generatorPartitionRectangles 89 9
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 4
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 89 10
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 5
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 89 11
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 4
    terms := 2
    radialRoot := generatorRadialRoots 1 58
  },
  {
    rectangle := generatorPartitionRectangles 89 12
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates15 1
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 89 13
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates16 5
    terms := 1
    radialRoot := generatorRadialRoots 1 58
  },
  {
    rectangle := generatorPartitionRectangles 89 14
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates16 4
    terms := 1
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 89 15
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates16 5
    terms := 1
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 89 16
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates16 4
    terms := 1
    radialRoot := generatorRadialRoots 1 56
  },
  {
    rectangle := generatorPartitionRectangles 89 17
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 3
    terms := 1
    radialRoot := generatorRadialRoots 1 62
  },
  {
    rectangle := generatorPartitionRectangles 89 18
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 2
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 89 19
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 3
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 89 20
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 2
    terms := 1
    radialRoot := generatorRadialRoots 1 60
  },
  {
    rectangle := generatorPartitionRectangles 89 21
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 1
    terms := 1
    radialRoot := generatorRadialRoots 1 60
  },
  {
    rectangle := generatorPartitionRectangles 89 22
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 0
    terms := 1
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 89 23
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 1
    terms := 1
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 89 24
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 0
    terms := 1
    radialRoot := generatorRadialRoots 1 58
  },
  {
    rectangle := generatorPartitionRectangles 89 25
    coordinateU := generatorCoordinates24 5
    coordinateV := generatorCoordinates16 3
    terms := 2
    radialRoot := generatorRadialRoots 1 60
  },
  {
    rectangle := generatorPartitionRectangles 89 26
    coordinateU := generatorCoordinates24 5
    coordinateV := generatorCoordinates16 2
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 89 27
    coordinateU := generatorCoordinates24 4
    coordinateV := generatorCoordinates16 3
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 89 28
    coordinateU := generatorCoordinates24 4
    coordinateV := generatorCoordinates16 2
    terms := 3
    radialRoot := generatorRadialRoots 1 58
  },
  {
    rectangle := generatorPartitionRectangles 89 29
    coordinateU := generatorCoordinates24 5
    coordinateV := generatorCoordinates16 1
    terms := 2
    radialRoot := generatorRadialRoots 1 58
  },
  {
    rectangle := generatorPartitionRectangles 89 30
    coordinateU := generatorCoordinates24 5
    coordinateV := generatorCoordinates16 0
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 89 31
    coordinateU := generatorCoordinates24 4
    coordinateV := generatorCoordinates16 1
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 89 32
    coordinateU := generatorCoordinates24 4
    coordinateV := generatorCoordinates16 0
    terms := 2
    radialRoot := generatorRadialRoots 1 56
  },
  {
    rectangle := generatorPartitionRectangles 89 33
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 89 34
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 89 35
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 89 36
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 89 37
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 3
    terms := 3
    radialRoot := generatorRadialRoots 1 58
  },
  {
    rectangle := generatorPartitionRectangles 89 38
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 2
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 89 39
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 3
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 89 40
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 2
    terms := 3
    radialRoot := generatorRadialRoots 1 56
  },
  {
    rectangle := generatorPartitionRectangles 89 41
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 1
    terms := 3
    radialRoot := generatorRadialRoots 1 56
  },
  {
    rectangle := generatorPartitionRectangles 89 42
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates16 0
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 89 43
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 1
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 89 44
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates16 0
    terms := 3
    radialRoot := generatorRadialRoots 1 54
  },
  {
    rectangle := generatorPartitionRectangles 89 45
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates16 3
    terms := 2
    radialRoot := generatorRadialRoots 1 56
  },
  {
    rectangle := generatorPartitionRectangles 89 46
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates16 2
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 89 47
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates16 3
    terms := 1
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 89 48
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates16 2
    terms := 1
    radialRoot := generatorRadialRoots 1 54
  },
  {
    rectangle := generatorPartitionRectangles 89 49
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates16 1
    terms := 2
    radialRoot := generatorRadialRoots 1 54
  },
  {
    rectangle := generatorPartitionRectangles 89 50
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates16 0
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 89 51
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates16 1
    terms := 1
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 89 52
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates16 0
    terms := 1
    radialRoot := generatorRadialRoots 1 52
  },
  {
    rectangle := generatorPartitionRectangles 89 53
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates15 7
    terms := 3
    radialRoot := generatorRadialRoots 1 54
  },
  {
    rectangle := generatorPartitionRectangles 89 54
    coordinateU := generatorCoordinates24 3
    coordinateV := generatorCoordinates15 6
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 89 55
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates15 7
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 89 56
    coordinateU := generatorCoordinates24 2
    coordinateV := generatorCoordinates15 6
    terms := 2
    radialRoot := generatorRadialRoots 1 52
  },
  {
    rectangle := generatorPartitionRectangles 89 57
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 89 58
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates15 7
    terms := 2
    radialRoot := generatorRadialRoots 1 52
  },
  {
    rectangle := generatorPartitionRectangles 89 59
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates15 6
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 89 60
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates15 7
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 89 61
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates15 6
    terms := 1
    radialRoot := generatorRadialRoots 1 50
  },
  {
    rectangle := generatorPartitionRectangles 89 62
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates15 5
    terms := 2
    radialRoot := generatorRadialRoots 1 50
  },
  {
    rectangle := generatorPartitionRectangles 89 63
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates15 4
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks89_valid : ∀ i, (generatorLeafBlocks89 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks89 i).coordinateU.IsValid ∧
      (generatorLeafBlocks89 i).coordinateV.IsValid ∧
      (generatorLeafBlocks89 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 7, generatorRadialRoots_valid 1 62⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 6, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 7, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 6, generatorRadialRoots_valid 1 60⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 1 60⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 58⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 1 58⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 56⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 62⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 60⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 60⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 58⟩
    · exact ⟨generatorCoordinates24_valid 5,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 60⟩
    · exact ⟨generatorCoordinates24_valid 5,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates24_valid 4,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates24_valid 4,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 58⟩
    · exact ⟨generatorCoordinates24_valid 5,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 58⟩
    · exact ⟨generatorCoordinates24_valid 5,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates24_valid 4,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates24_valid 4,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 56⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 58⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 56⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 56⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 54⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 56⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 1 54⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 54⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates16_valid 1, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates16_valid 0, generatorRadialRoots_valid 1 52⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates15_valid 7, generatorRadialRoots_valid 1 54⟩
    · exact ⟨generatorCoordinates24_valid 3,
        generatorCoordinates15_valid 6, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates15_valid 7, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates24_valid 2,
        generatorCoordinates15_valid 6, generatorRadialRoots_valid 1 52⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates15_valid 7, generatorRadialRoots_valid 1 52⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates15_valid 6, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates15_valid 7, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates15_valid 6, generatorRadialRoots_valid 1 50⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates15_valid 5, generatorRadialRoots_valid 1 50⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates15_valid 4, generatorRadialRoots_valid 1 49⟩
  have hMeta : ∀ i, (generatorLeafBlocks89 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks89 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
