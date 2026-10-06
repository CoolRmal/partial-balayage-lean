/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates58
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates60

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 26 of the recorded finite partition. -/
def generatorLeafBlocks26 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 26 0
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates34 1
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 26 1
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 26 2
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates34 3
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 26 3
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 26 4
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates34 3
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 26 5
    coordinateU := generatorCoordinates61 7
    coordinateV := generatorCoordinates36 0
    terms := 12
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 26 6
    coordinateU := generatorCoordinates61 7
    coordinateV := generatorCoordinates35 7
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 26 7
    coordinateU := generatorCoordinates61 6
    coordinateV := generatorCoordinates36 0
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 26 8
    coordinateU := generatorCoordinates61 6
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 26 9
    coordinateU := generatorCoordinates61 7
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 26 10
    coordinateU := generatorCoordinates61 7
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 11
    coordinateU := generatorCoordinates61 6
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 12
    coordinateU := generatorCoordinates61 6
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 26 13
    coordinateU := generatorCoordinates61 5
    coordinateV := generatorCoordinates36 0
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 26 14
    coordinateU := generatorCoordinates61 5
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 15
    coordinateU := generatorCoordinates61 4
    coordinateV := generatorCoordinates36 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 16
    coordinateU := generatorCoordinates61 4
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 26 17
    coordinateU := generatorCoordinates61 5
    coordinateV := generatorCoordinates35 6
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 26 18
    coordinateU := generatorCoordinates61 5
    coordinateV := generatorCoordinates35 5
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 19
    coordinateU := generatorCoordinates61 4
    coordinateV := generatorCoordinates35 6
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 20
    coordinateU := generatorCoordinates61 4
    coordinateV := generatorCoordinates35 5
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 26 21
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 26 22
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 23
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates34 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 24
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 25
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates33 1
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 26
    coordinateU := generatorCoordinates61 7
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 26 27
    coordinateU := generatorCoordinates61 7
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 28
    coordinateU := generatorCoordinates61 6
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 29
    coordinateU := generatorCoordinates61 6
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 26 30
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates33 7
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 31
    coordinateU := generatorCoordinates61 5
    coordinateV := generatorCoordinates35 4
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 26 32
    coordinateU := generatorCoordinates61 5
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 33
    coordinateU := generatorCoordinates61 4
    coordinateV := generatorCoordinates35 4
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 34
    coordinateU := generatorCoordinates61 4
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 26 35
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates33 7
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 26 36
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 26 37
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 26 38
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 26 39
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 26 40
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 26 41
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates34 3
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 42
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 26 43
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 44
    coordinateU := generatorCoordinates61 3
    coordinateV := generatorCoordinates36 0
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 26 45
    coordinateU := generatorCoordinates61 3
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 46
    coordinateU := generatorCoordinates61 2
    coordinateV := generatorCoordinates36 0
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 47
    coordinateU := generatorCoordinates61 2
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 26 48
    coordinateU := generatorCoordinates61 3
    coordinateV := generatorCoordinates35 6
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 26 49
    coordinateU := generatorCoordinates61 3
    coordinateV := generatorCoordinates35 5
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 50
    coordinateU := generatorCoordinates61 2
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 51
    coordinateU := generatorCoordinates61 2
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 26 52
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates34 2
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 53
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates34 1
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 26 54
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates34 4
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 26 55
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 56
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates34 4
    terms := 8
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 26 57
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates34 3
    terms := 8
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 26 58
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates33 3
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 26 59
    coordinateU := generatorCoordinates61 3
    coordinateV := generatorCoordinates35 4
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 26 60
    coordinateU := generatorCoordinates61 3
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 26 61
    coordinateU := generatorCoordinates61 2
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 26 62
    coordinateU := generatorCoordinates61 2
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 26 63
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates33 7
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks26_valid : ∀ i, (generatorLeafBlocks26 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks26 i).coordinateU.IsValid ∧
      (generatorLeafBlocks26 i).coordinateV.IsValid ∧
      (generatorLeafBlocks26 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates61_valid 7,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates61_valid 7,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates61_valid 6,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates61_valid 6,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates61_valid 7,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates61_valid 7,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates61_valid 6,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates61_valid 6,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates61_valid 5,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates61_valid 5,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates61_valid 4,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates61_valid 4,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates61_valid 5,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates61_valid 5,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 4,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 4,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates61_valid 7,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates61_valid 7,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 6,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 6,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates61_valid 5,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates61_valid 5,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates61_valid 4,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates61_valid 4,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 3,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates61_valid 3,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 2,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 2,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates61_valid 3,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates61_valid 3,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates61_valid 2,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates61_valid 2,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates61_valid 3,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates61_valid 3,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates61_valid 2,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates61_valid 2,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 48⟩
  have hMeta : ∀ i, (generatorLeafBlocks26 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks26 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
