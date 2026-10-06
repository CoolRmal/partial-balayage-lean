/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 70 of the recorded finite partition. -/
def generatorLeafBlocks70 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 70 0
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 70 1
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 70 2
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 70 3
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 70 4
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 70 5
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 70 6
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 70 7
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates23 0
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 70 8
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 70 9
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates23 0
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 70 10
    coordinateU := generatorCoordinates33 4
    coordinateV := generatorCoordinates22 0
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 70 11
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 70 12
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates23 0
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 70 13
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 70 14
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates23 0
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 70 15
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates22 0
    terms := 4
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 70 16
    coordinateU := generatorCoordinates33 4
    coordinateV := generatorCoordinates21 7
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 70 17
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 70 18
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 58
  },
  {
    rectangle := generatorPartitionRectangles 70 19
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 70 20
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 70 21
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 56
  },
  {
    rectangle := generatorPartitionRectangles 70 22
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 70 23
    coordinateU := generatorCoordinates36 2
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 56
  },
  {
    rectangle := generatorPartitionRectangles 70 24
    coordinateU := generatorCoordinates36 2
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 70 25
    coordinateU := generatorCoordinates36 1
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 70 26
    coordinateU := generatorCoordinates36 1
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 54
  },
  {
    rectangle := generatorPartitionRectangles 70 27
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates21 7
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 70 28
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 70 29
    coordinateU := generatorCoordinates36 0
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 54
  },
  {
    rectangle := generatorPartitionRectangles 70 30
    coordinateU := generatorCoordinates36 0
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 70 31
    coordinateU := generatorCoordinates35 7
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 70 32
    coordinateU := generatorCoordinates35 7
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 52
  },
  {
    rectangle := generatorPartitionRectangles 70 33
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 70 34
    coordinateU := generatorCoordinates35 6
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 52
  },
  {
    rectangle := generatorPartitionRectangles 70 35
    coordinateU := generatorCoordinates35 6
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 70 36
    coordinateU := generatorCoordinates35 5
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 70 37
    coordinateU := generatorCoordinates35 5
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 50
  },
  {
    rectangle := generatorPartitionRectangles 70 38
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 70 39
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 70 40
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 70 41
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 70 42
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates22 0
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 70 43
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 70 44
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 70 45
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 70 46
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 70 47
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates22 0
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 70 48
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates21 7
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 70 49
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 70 50
    coordinateU := generatorCoordinates35 4
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 50
  },
  {
    rectangle := generatorPartitionRectangles 70 51
    coordinateU := generatorCoordinates35 4
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 70 52
    coordinateU := generatorCoordinates35 3
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 70 53
    coordinateU := generatorCoordinates35 3
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 48
  },
  {
    rectangle := generatorPartitionRectangles 70 54
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 70 55
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 70 56
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates21 7
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 70 57
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 70 58
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates22 2
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 70 59
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 70 60
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates22 2
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 70 61
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 56
  },
  {
    rectangle := generatorPartitionRectangles 70 62
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 70 63
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks70_valid : ∀ i, (generatorLeafBlocks70 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks70 i).coordinateU.IsValid ∧
      (generatorLeafBlocks70 i).coordinateV.IsValid ∧
      (generatorLeafBlocks70 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates33_valid 4,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates33_valid 4,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 58⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 56⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates36_valid 2,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 56⟩
    · exact ⟨generatorCoordinates36_valid 2,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates36_valid 1,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates36_valid 1,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 54⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates36_valid 0,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 54⟩
    · exact ⟨generatorCoordinates36_valid 0,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates35_valid 7,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates35_valid 7,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 52⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates35_valid 6,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 52⟩
    · exact ⟨generatorCoordinates35_valid 6,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates35_valid 5,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates35_valid 5,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 50⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates35_valid 4,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 50⟩
    · exact ⟨generatorCoordinates35_valid 4,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates35_valid 3,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates35_valid 3,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 48⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 56⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 55⟩
  have hMeta : ∀ i, (generatorLeafBlocks70 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks70 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
