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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates2
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates3
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates80
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates82

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 2 of the recorded finite partition. -/
def generatorLeafBlocks2 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 2 0
    coordinateU := generatorCoordinates81 6
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 2 1
    coordinateU := generatorCoordinates80 7
    coordinateV := generatorCoordinates5 5
    terms := 3
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 2 2
    coordinateU := generatorCoordinates80 7
    coordinateV := generatorCoordinates5 4
    terms := 5
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 2 3
    coordinateU := generatorCoordinates80 6
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 2 4
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates6 3
    terms := 4
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 2 5
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates6 2
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 2 6
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates6 3
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 2 7
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates6 2
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 2 8
    coordinateU := generatorCoordinates80 7
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 2 9
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 2 10
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 11
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 12
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 13
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates6 1
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 2 14
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates6 0
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 15
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates6 1
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 16
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates6 0
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 17
    coordinateU := generatorCoordinates80 6
    coordinateV := generatorCoordinates5 2
    terms := 30
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 18
    coordinateU := generatorCoordinates82 1
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 2 19
    coordinateU := generatorCoordinates82 1
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 2 20
    coordinateU := generatorCoordinates82 0
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 2 21
    coordinateU := generatorCoordinates82 0
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 2 22
    coordinateU := generatorCoordinates82 1
    coordinateV := generatorCoordinates1 4
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 2 23
    coordinateU := generatorCoordinates82 1
    coordinateV := generatorCoordinates1 3
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 24
    coordinateU := generatorCoordinates82 0
    coordinateV := generatorCoordinates1 4
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 25
    coordinateU := generatorCoordinates82 0
    coordinateV := generatorCoordinates1 3
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 26
    coordinateU := generatorCoordinates81 7
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 2 27
    coordinateU := generatorCoordinates82 7
    coordinateV := generatorCoordinates3 4
    terms := 20
    radialRoot := generatorRadialRoots 5 3
  },
  {
    rectangle := generatorPartitionRectangles 2 28
    coordinateU := generatorCoordinates82 7
    coordinateV := generatorCoordinates3 3
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 29
    coordinateU := generatorCoordinates82 6
    coordinateV := generatorCoordinates3 4
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 30
    coordinateU := generatorCoordinates82 6
    coordinateV := generatorCoordinates3 3
    terms := 20
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 2 31
    coordinateU := generatorCoordinates81 6
    coordinateV := generatorCoordinates1 6
    terms := 30
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 2 32
    coordinateU := generatorCoordinates82 5
    coordinateV := generatorCoordinates3 4
    terms := 20
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 2 33
    coordinateU := generatorCoordinates82 5
    coordinateV := generatorCoordinates3 3
    terms := 30
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 34
    coordinateU := generatorCoordinates82 4
    coordinateV := generatorCoordinates3 4
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 35
    coordinateU := generatorCoordinates82 4
    coordinateV := generatorCoordinates3 3
    terms := 30
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 2 36
    coordinateU := generatorCoordinates82 7
    coordinateV := generatorCoordinates3 2
    terms := 20
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 2 37
    coordinateU := generatorCoordinates82 7
    coordinateV := generatorCoordinates3 1
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 38
    coordinateU := generatorCoordinates82 6
    coordinateV := generatorCoordinates3 2
    terms := 30
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 39
    coordinateU := generatorCoordinates82 6
    coordinateV := generatorCoordinates3 1
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 2 40
    coordinateU := generatorCoordinates81 7
    coordinateV := generatorCoordinates1 3
    terms := 30
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 41
    coordinateU := generatorCoordinates82 5
    coordinateV := generatorCoordinates3 2
    terms := 30
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 2 42
    coordinateU := generatorCoordinates82 5
    coordinateV := generatorCoordinates3 1
    terms := 30
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 43
    coordinateU := generatorCoordinates82 4
    coordinateV := generatorCoordinates3 2
    terms := 30
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 44
    coordinateU := generatorCoordinates82 4
    coordinateV := generatorCoordinates3 1
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 2 45
    coordinateU := generatorCoordinates82 5
    coordinateV := generatorCoordinates3 0
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 2 46
    coordinateU := generatorCoordinates82 5
    coordinateV := generatorCoordinates2 7
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 2 47
    coordinateU := generatorCoordinates82 4
    coordinateV := generatorCoordinates3 0
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 2 48
    coordinateU := generatorCoordinates82 4
    coordinateV := generatorCoordinates2 7
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 2 49
    coordinateU := generatorCoordinates81 1
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 50
    coordinateU := generatorCoordinates81 1
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 2 51
    coordinateU := generatorCoordinates81 7
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 2 52
    coordinateU := generatorCoordinates81 7
    coordinateV := generatorCoordinates1 1
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 2 53
    coordinateU := generatorCoordinates81 6
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 2 54
    coordinateU := generatorCoordinates81 6
    coordinateV := generatorCoordinates1 1
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 2 55
    coordinateU := generatorCoordinates81 0
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 2 56
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 2 57
    coordinateU := generatorCoordinates82 3
    coordinateV := generatorCoordinates3 4
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 2 58
    coordinateU := generatorCoordinates82 3
    coordinateV := generatorCoordinates3 3
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 59
    coordinateU := generatorCoordinates82 2
    coordinateV := generatorCoordinates3 4
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 60
    coordinateU := generatorCoordinates82 2
    coordinateV := generatorCoordinates3 3
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 2 61
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 2 62
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 2 63
    coordinateU := generatorCoordinates82 3
    coordinateV := generatorCoordinates3 2
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks2_valid : ∀ i, (generatorLeafBlocks2 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks2 i).coordinateU.IsValid ∧
      (generatorLeafBlocks2 i).coordinateV.IsValid ∧
      (generatorLeafBlocks2 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates81_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates80_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates80_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates80_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates80_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates80_valid 6,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates82_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates82_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates82_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates82_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates82_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates82_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates82_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates82_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates81_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates82_valid 7,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 5 3⟩
    · exact ⟨generatorCoordinates82_valid 7,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates82_valid 6,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates82_valid 6,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates81_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates82_valid 5,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates82_valid 5,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates82_valid 4,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates82_valid 4,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates82_valid 7,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates82_valid 7,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates82_valid 6,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates82_valid 6,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates81_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates82_valid 5,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates82_valid 5,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates82_valid 4,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates82_valid 4,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates82_valid 5,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates82_valid 5,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates82_valid 4,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates82_valid 4,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates81_valid 1,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates81_valid 1,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates81_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates81_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates81_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates81_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates81_valid 0,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates82_valid 3,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates82_valid 3,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates82_valid 2,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates82_valid 2,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates82_valid 3,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 4 61⟩
  have hMeta : ∀ i, (generatorLeafBlocks2 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks2 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
