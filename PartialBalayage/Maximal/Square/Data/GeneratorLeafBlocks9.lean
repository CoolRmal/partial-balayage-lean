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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates72
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates74

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 9 of the recorded finite partition. -/
def generatorLeafBlocks9 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 9 0
    coordinateU := generatorCoordinates73 7
    coordinateV := generatorCoordinates15 3
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 9 1
    coordinateU := generatorCoordinates73 7
    coordinateV := generatorCoordinates15 2
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 9 2
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates15 1
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 9 3
    coordinateU := generatorCoordinates75 0
    coordinateV := generatorCoordinates16 5
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 9 4
    coordinateU := generatorCoordinates75 0
    coordinateV := generatorCoordinates16 4
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 5
    coordinateU := generatorCoordinates74 7
    coordinateV := generatorCoordinates16 5
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 6
    coordinateU := generatorCoordinates74 7
    coordinateV := generatorCoordinates16 4
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 9 7
    coordinateU := generatorCoordinates74 6
    coordinateV := generatorCoordinates16 7
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 9 8
    coordinateU := generatorCoordinates74 6
    coordinateV := generatorCoordinates16 6
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 9
    coordinateU := generatorCoordinates74 5
    coordinateV := generatorCoordinates16 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 10
    coordinateU := generatorCoordinates74 5
    coordinateV := generatorCoordinates16 6
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 9 11
    coordinateU := generatorCoordinates74 6
    coordinateV := generatorCoordinates16 5
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 9 12
    coordinateU := generatorCoordinates74 6
    coordinateV := generatorCoordinates16 4
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 9 13
    coordinateU := generatorCoordinates74 5
    coordinateV := generatorCoordinates16 5
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 9 14
    coordinateU := generatorCoordinates74 5
    coordinateV := generatorCoordinates16 4
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 9 15
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates14 7
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 9 16
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates14 6
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 17
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates14 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 18
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates14 6
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 9 19
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates14 5
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 9 20
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates14 4
    terms := 8
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 21
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates14 5
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 22
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates14 4
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 9 23
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates14 7
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 9 24
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates14 6
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 25
    coordinateU := generatorCoordinates74 6
    coordinateV := generatorCoordinates16 3
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 9 26
    coordinateU := generatorCoordinates74 6
    coordinateV := generatorCoordinates16 2
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 27
    coordinateU := generatorCoordinates74 5
    coordinateV := generatorCoordinates16 3
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 28
    coordinateU := generatorCoordinates74 5
    coordinateV := generatorCoordinates16 2
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 9 29
    coordinateU := generatorCoordinates73 7
    coordinateV := generatorCoordinates14 6
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 9 30
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates14 5
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 9 31
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates14 4
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 9 32
    coordinateU := generatorCoordinates73 7
    coordinateV := generatorCoordinates14 5
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 9 33
    coordinateU := generatorCoordinates73 7
    coordinateV := generatorCoordinates14 4
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 9 34
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates15 3
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 9 35
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates15 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 36
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates15 3
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 9 37
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates15 2
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 9 38
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates15 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 9 39
    coordinateU := generatorCoordinates74 4
    coordinateV := generatorCoordinates16 5
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 9 40
    coordinateU := generatorCoordinates74 4
    coordinateV := generatorCoordinates16 4
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 41
    coordinateU := generatorCoordinates74 3
    coordinateV := generatorCoordinates16 5
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 42
    coordinateU := generatorCoordinates74 3
    coordinateV := generatorCoordinates16 4
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 9 43
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates15 1
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 44
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates15 0
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 9 45
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates14 3
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 9 46
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates15 1
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 9 47
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates15 0
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 9 48
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates15 1
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 9 49
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates15 0
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 9 50
    coordinateU := generatorCoordinates74 4
    coordinateV := generatorCoordinates16 3
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 9 51
    coordinateU := generatorCoordinates74 4
    coordinateV := generatorCoordinates16 2
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 9 52
    coordinateU := generatorCoordinates74 3
    coordinateV := generatorCoordinates16 3
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 9 53
    coordinateU := generatorCoordinates74 3
    coordinateV := generatorCoordinates16 2
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 9 54
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates14 6
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 9 55
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates14 7
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 9 56
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates14 6
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 9 57
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates14 5
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 9 58
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates14 4
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 9 59
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates14 5
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 9 60
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates14 4
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 9 61
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates14 7
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 9 62
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates14 6
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 9 63
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates14 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks9_valid : ∀ i, (generatorLeafBlocks9 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks9 i).coordinateU.IsValid ∧
      (generatorLeafBlocks9 i).coordinateV.IsValid ∧
      (generatorLeafBlocks9 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates73_valid 7,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates73_valid 7,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates75_valid 0,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates75_valid 0,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates74_valid 7,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates74_valid 7,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates74_valid 6,
        generatorCoordinates16_valid 7, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates74_valid 6,
        generatorCoordinates16_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates74_valid 5,
        generatorCoordinates16_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates74_valid 5,
        generatorCoordinates16_valid 6, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates74_valid 6,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates74_valid 6,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates74_valid 5,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates74_valid 5,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates74_valid 6,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates74_valid 6,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates74_valid 5,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates74_valid 5,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates73_valid 7,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates73_valid 7,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates73_valid 7,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates74_valid 4,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates74_valid 4,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates74_valid 3,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates74_valid 3,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates74_valid 4,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates74_valid 4,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates74_valid 3,
        generatorCoordinates16_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates74_valid 3,
        generatorCoordinates16_valid 2, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 4 42⟩
  have hMeta : ∀ i, (generatorLeafBlocks9 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks9 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
