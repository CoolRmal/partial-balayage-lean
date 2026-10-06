/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates1
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates7
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates16
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates17

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 99 of the recorded finite partition. -/
def generatorLeafBlocks99 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 99 0
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates7 0
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 1
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates7 1
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 2
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates7 0
    terms := 0
    radialRoot := generatorRadialRoots 0 60
  },
  {
    rectangle := generatorPartitionRectangles 99 3
    coordinateU := generatorCoordinates17 3
    coordinateV := generatorCoordinates6 7
    terms := 0
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 99 4
    coordinateU := generatorCoordinates17 3
    coordinateV := generatorCoordinates6 6
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 99 5
    coordinateU := generatorCoordinates17 2
    coordinateV := generatorCoordinates6 7
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 99 6
    coordinateU := generatorCoordinates17 2
    coordinateV := generatorCoordinates6 6
    terms := 0
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 99 7
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 99 8
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates6 7
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 99 9
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates6 6
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 99 10
    coordinateU := generatorCoordinates17 0
    coordinateV := generatorCoordinates6 7
    terms := 2
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 99 11
    coordinateU := generatorCoordinates17 0
    coordinateV := generatorCoordinates6 6
    terms := 1
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 99 12
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 13
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 14
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 15
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 16
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 99 17
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates6 7
    terms := 3
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 99 18
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates6 6
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 19
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates6 7
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 20
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates6 6
    terms := 1
    radialRoot := generatorRadialRoots 0 60
  },
  {
    rectangle := generatorPartitionRectangles 99 21
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 22
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates6 7
    terms := 1
    radialRoot := generatorRadialRoots 0 60
  },
  {
    rectangle := generatorPartitionRectangles 99 23
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates6 6
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 24
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates6 7
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 25
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates6 6
    terms := 0
    radialRoot := generatorRadialRoots 0 58
  },
  {
    rectangle := generatorPartitionRectangles 99 26
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 99 27
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 99 28
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 29
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 30
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 99 31
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 99 32
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates6 4
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 99 33
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 99 34
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates6 4
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 35
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates6 3
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 99 36
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates6 2
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 37
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates6 3
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 38
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates6 2
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 99 39
    coordinateU := generatorCoordinates14 0
    coordinateV := generatorCoordinates5 5
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 99 40
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates6 3
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 99 41
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates6 2
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 42
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates6 3
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 43
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates6 2
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 99 44
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates6 1
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 99 45
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 46
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates6 1
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 47
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 99 48
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 99 49
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 99 50
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 99 51
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 99 52
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates6 1
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 99 53
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 99 54
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates6 1
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 99 55
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 99 56
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 99 57
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 99 58
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 99 59
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 99 60
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 99 61
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 62
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 99 63
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks99_valid : ∀ i, (generatorLeafBlocks99 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks99 i).coordinateU.IsValid ∧
      (generatorLeafBlocks99 i).coordinateV.IsValid ∧
      (generatorLeafBlocks99 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 0 60⟩
    · exact ⟨generatorCoordinates17_valid 3,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates17_valid 3,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates17_valid 2,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates17_valid 2,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates17_valid 0,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates17_valid 0,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 0 60⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 0 60⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 0 58⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates14_valid 0,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 55⟩
  have hMeta : ∀ i, (generatorLeafBlocks99 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks99 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
