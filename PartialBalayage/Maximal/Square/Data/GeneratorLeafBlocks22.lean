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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates62
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates64

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 22 of the recorded finite partition. -/
def generatorLeafBlocks22 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 22 0
    coordinateU := generatorCoordinates64 1
    coordinateV := generatorCoordinates31 6
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 22 1
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 22 2
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 22 3
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates30 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 22 4
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 22 5
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates29 2
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 6
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates30 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 22 7
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates30 0
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 8
    coordinateU := generatorCoordinates64 2
    coordinateV := generatorCoordinates31 5
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 22 9
    coordinateU := generatorCoordinates64 2
    coordinateV := generatorCoordinates31 4
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 10
    coordinateU := generatorCoordinates64 1
    coordinateV := generatorCoordinates31 5
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 11
    coordinateU := generatorCoordinates64 1
    coordinateV := generatorCoordinates31 4
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 22 12
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates30 0
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 22 13
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 22 14
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 22 15
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 22 16
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 22 17
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 22 18
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 22 19
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 22 20
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 22 21
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates30 3
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 22 22
    coordinateU := generatorCoordinates64 0
    coordinateV := generatorCoordinates31 7
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 22 23
    coordinateU := generatorCoordinates64 0
    coordinateV := generatorCoordinates31 6
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 24
    coordinateU := generatorCoordinates63 7
    coordinateV := generatorCoordinates31 7
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 25
    coordinateU := generatorCoordinates63 7
    coordinateV := generatorCoordinates31 6
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 22 26
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates30 3
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 27
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates30 2
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 22 28
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates29 5
    terms := 50
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 22 29
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 22 30
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 22 31
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 22 32
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 22 33
    coordinateU := generatorCoordinates64 0
    coordinateV := generatorCoordinates31 5
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 22 34
    coordinateU := generatorCoordinates64 0
    coordinateV := generatorCoordinates31 4
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 22 35
    coordinateU := generatorCoordinates63 7
    coordinateV := generatorCoordinates31 5
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 22 36
    coordinateU := generatorCoordinates63 7
    coordinateV := generatorCoordinates31 4
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 22 37
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates30 0
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 22 38
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates30 1
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 22 39
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates30 0
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 22 40
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 22 41
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 22 42
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 22 43
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 22 44
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 22 45
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 22 46
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 22 47
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 22 48
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 22 49
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 22 50
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 22 51
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 22 52
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 22 53
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 22 54
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 22 55
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 22 56
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 22 57
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 22 58
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 22 59
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates25 6
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 22 60
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates25 5
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 22 61
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 22 62
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 22 63
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates25 4
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks22_valid : ∀ i, (generatorLeafBlocks22 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks22 i).coordinateU.IsValid ∧
      (generatorLeafBlocks22 i).coordinateV.IsValid ∧
      (generatorLeafBlocks22 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates64_valid 1,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates64_valid 2,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates64_valid 2,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates64_valid 1,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates64_valid 1,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates64_valid 0,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates64_valid 0,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates63_valid 7,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates63_valid 7,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates64_valid 0,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates64_valid 0,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates63_valid 7,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates63_valid 7,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 26⟩
  have hMeta : ∀ i, (generatorLeafBlocks22 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks22 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
