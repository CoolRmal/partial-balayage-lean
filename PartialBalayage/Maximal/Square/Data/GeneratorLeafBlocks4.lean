/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates7
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates78
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates80

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 4 of the recorded finite partition. -/
def generatorLeafBlocks4 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 4 0
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates10 4
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 4 1
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates10 3
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 2
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates10 2
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 3
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates10 1
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 4
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates10 2
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 5
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates10 1
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 4 6
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates6 5
    terms := 8
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 4 7
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates6 4
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 4 8
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates6 5
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 4 9
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates6 4
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 4 10
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates6 3
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 4 11
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates6 2
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 4 12
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates6 3
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 4 13
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates6 2
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 14
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates6 5
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 4 15
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 4 16
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates6 5
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 4 17
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 18
    coordinateU := generatorCoordinates80 2
    coordinateV := generatorCoordinates7 3
    terms := 12
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 4 19
    coordinateU := generatorCoordinates80 2
    coordinateV := generatorCoordinates7 2
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 20
    coordinateU := generatorCoordinates80 1
    coordinateV := generatorCoordinates7 3
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 21
    coordinateU := generatorCoordinates80 1
    coordinateV := generatorCoordinates7 2
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 4 22
    coordinateU := generatorCoordinates80 2
    coordinateV := generatorCoordinates7 1
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 4 23
    coordinateU := generatorCoordinates80 2
    coordinateV := generatorCoordinates7 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 24
    coordinateU := generatorCoordinates80 1
    coordinateV := generatorCoordinates7 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 25
    coordinateU := generatorCoordinates80 1
    coordinateV := generatorCoordinates7 0
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 4 26
    coordinateU := generatorCoordinates80 0
    coordinateV := generatorCoordinates7 3
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 4 27
    coordinateU := generatorCoordinates80 0
    coordinateV := generatorCoordinates7 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 28
    coordinateU := generatorCoordinates79 7
    coordinateV := generatorCoordinates7 3
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 29
    coordinateU := generatorCoordinates79 7
    coordinateV := generatorCoordinates7 2
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 4 30
    coordinateU := generatorCoordinates80 0
    coordinateV := generatorCoordinates7 1
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 4 31
    coordinateU := generatorCoordinates80 0
    coordinateV := generatorCoordinates7 0
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 4 32
    coordinateU := generatorCoordinates79 7
    coordinateV := generatorCoordinates7 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 4 33
    coordinateU := generatorCoordinates79 7
    coordinateV := generatorCoordinates7 0
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 4 34
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates6 1
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 35
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates6 0
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 36
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates6 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 37
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates6 0
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 4 38
    coordinateU := generatorCoordinates78 4
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 39
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates6 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 4 40
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates6 0
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 41
    coordinateU := generatorCoordinates80 0
    coordinateV := generatorCoordinates6 7
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 4 42
    coordinateU := generatorCoordinates80 0
    coordinateV := generatorCoordinates6 6
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 43
    coordinateU := generatorCoordinates79 7
    coordinateV := generatorCoordinates6 7
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 44
    coordinateU := generatorCoordinates79 7
    coordinateV := generatorCoordinates6 6
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 4 45
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates6 0
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 4 46
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates5 7
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 4 47
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 4 48
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates5 7
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 4 49
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 4 50
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates6 5
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 4 51
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 52
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates6 5
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 4 53
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 4 54
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates6 3
    terms := 75
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 4 55
    coordinateU := generatorCoordinates79 6
    coordinateV := generatorCoordinates7 1
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 4 56
    coordinateU := generatorCoordinates79 6
    coordinateV := generatorCoordinates7 0
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 57
    coordinateU := generatorCoordinates79 5
    coordinateV := generatorCoordinates7 1
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 58
    coordinateU := generatorCoordinates79 5
    coordinateV := generatorCoordinates7 0
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 4 59
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates6 3
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 60
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates6 2
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 4 61
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates5 5
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 4 62
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates6 3
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 4 63
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates6 2
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks4_valid : ∀ i, (generatorLeafBlocks4 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks4 i).coordinateU.IsValid ∧
      (generatorLeafBlocks4 i).coordinateV.IsValid ∧
      (generatorLeafBlocks4 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates80_valid 2,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates80_valid 2,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates80_valid 1,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates80_valid 1,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates80_valid 2,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates80_valid 2,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates80_valid 1,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates80_valid 1,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates80_valid 0,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates80_valid 0,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates79_valid 7,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates79_valid 7,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates80_valid 0,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates80_valid 0,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates79_valid 7,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates79_valid 7,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates78_valid 4,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates80_valid 0,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates80_valid 0,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates79_valid 7,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates79_valid 7,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates79_valid 6,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates79_valid 6,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates79_valid 5,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates79_valid 5,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 4 48⟩
  have hMeta : ∀ i, (generatorLeafBlocks4 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks4 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
