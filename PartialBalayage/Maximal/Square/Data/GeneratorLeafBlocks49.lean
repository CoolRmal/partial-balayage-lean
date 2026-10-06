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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates48

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 49 of the recorded finite partition. -/
def generatorLeafBlocks49 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 49 0
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates36 0
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 49 1
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 7
    terms := 12
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 49 2
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 49 3
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 49 4
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 6
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 49 5
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 5
    terms := 12
    radialRoot := generatorRadialRoots 4 4
  },
  {
    rectangle := generatorPartitionRectangles 49 6
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 49 7
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates34 1
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 49 8
    coordinateU := generatorCoordinates48 7
    coordinateV := generatorCoordinates36 4
    terms := 12
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 49 9
    coordinateU := generatorCoordinates48 7
    coordinateV := generatorCoordinates36 3
    terms := 8
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 49 10
    coordinateU := generatorCoordinates48 6
    coordinateV := generatorCoordinates36 4
    terms := 8
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 49 11
    coordinateU := generatorCoordinates48 6
    coordinateV := generatorCoordinates36 3
    terms := 8
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 49 12
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 49 13
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates36 4
    terms := 8
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 49 14
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates36 3
    terms := 8
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 49 15
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates36 4
    terms := 8
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 49 16
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates36 3
    terms := 8
    radialRoot := generatorRadialRoots 4 4
  },
  {
    rectangle := generatorPartitionRectangles 49 17
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 49 18
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 49 19
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates34 1
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 49 20
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 49 21
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates34 1
    terms := 20
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 22
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 4
  },
  {
    rectangle := generatorPartitionRectangles 49 23
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 49 24
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 4
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 49 25
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 3
    terms := 12
    radialRoot := generatorRadialRoots 4 2
  },
  {
    rectangle := generatorPartitionRectangles 49 26
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 2
    terms := 20
    radialRoot := generatorRadialRoots 4 2
  },
  {
    rectangle := generatorPartitionRectangles 49 27
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 1
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 49 28
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 2
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 49 29
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 1
    terms := 12
    radialRoot := generatorRadialRoots 4 0
  },
  {
    rectangle := generatorPartitionRectangles 49 30
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 49 31
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 32
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 4 0
  },
  {
    rectangle := generatorPartitionRectangles 49 33
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates34 7
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 34
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 35
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates34 7
    terms := 12
    radialRoot := generatorRadialRoots 3 62
  },
  {
    rectangle := generatorPartitionRectangles 49 36
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates34 6
    terms := 12
    radialRoot := generatorRadialRoots 3 62
  },
  {
    rectangle := generatorPartitionRectangles 49 37
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates34 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 38
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates34 6
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 39
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates34 5
    terms := 12
    radialRoot := generatorRadialRoots 3 60
  },
  {
    rectangle := generatorPartitionRectangles 49 40
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 41
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 49 42
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 43
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 44
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 45
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 49 46
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 49 47
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 49 48
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 49 49
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 49 50
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates34 4
    terms := 20
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 49 51
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 49 52
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 49 53
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates34 3
    terms := 8
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 54
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 55
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates34 1
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 56
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 57
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates34 1
    terms := 20
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 49 58
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates34 4
    terms := 8
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 49 59
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates34 3
    terms := 8
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 60
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates34 4
    terms := 4
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 49 61
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates34 3
    terms := 5
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 49 62
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 49 63
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates34 1
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks49_valid : ∀ i, (generatorLeafBlocks49 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks49 i).coordinateU.IsValid ∧
      (generatorLeafBlocks49 i).coordinateV.IsValid ∧
      (generatorLeafBlocks49 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 4⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates48_valid 7,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates48_valid 7,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates48_valid 6,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates48_valid 6,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 4⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 4⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 2⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 4 2⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 4 0⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 4 0⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 3 62⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 62⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 60⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 57⟩
  have hMeta : ∀ i, (generatorLeafBlocks49 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks49 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
