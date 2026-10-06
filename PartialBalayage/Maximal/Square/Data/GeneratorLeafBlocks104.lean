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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates4
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates7
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates8
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 104 of the recorded finite partition. -/
def generatorLeafBlocks104 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 104 0
    coordinateU := generatorCoordinates7 6
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 15
  },
  {
    rectangle := generatorPartitionRectangles 104 1
    coordinateU := generatorCoordinates7 5
    coordinateV := generatorCoordinates2 2
    terms := 0
    radialRoot := generatorRadialRoots 0 19
  },
  {
    rectangle := generatorPartitionRectangles 104 2
    coordinateU := generatorCoordinates7 5
    coordinateV := generatorCoordinates2 1
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 3
    coordinateU := generatorCoordinates9 1
    coordinateV := generatorCoordinates4 4
    terms := 0
    radialRoot := generatorRadialRoots 0 18
  },
  {
    rectangle := generatorPartitionRectangles 104 4
    coordinateU := generatorCoordinates9 1
    coordinateV := generatorCoordinates4 3
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 5
    coordinateU := generatorCoordinates9 0
    coordinateV := generatorCoordinates4 4
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 6
    coordinateU := generatorCoordinates9 0
    coordinateV := generatorCoordinates4 3
    terms := 1
    radialRoot := generatorRadialRoots 0 16
  },
  {
    rectangle := generatorPartitionRectangles 104 7
    coordinateU := generatorCoordinates9 1
    coordinateV := generatorCoordinates4 2
    terms := 0
    radialRoot := generatorRadialRoots 0 16
  },
  {
    rectangle := generatorPartitionRectangles 104 8
    coordinateU := generatorCoordinates9 1
    coordinateV := generatorCoordinates4 1
    terms := 0
    radialRoot := generatorRadialRoots 0 15
  },
  {
    rectangle := generatorPartitionRectangles 104 9
    coordinateU := generatorCoordinates9 0
    coordinateV := generatorCoordinates4 2
    terms := 1
    radialRoot := generatorRadialRoots 0 15
  },
  {
    rectangle := generatorPartitionRectangles 104 10
    coordinateU := generatorCoordinates9 0
    coordinateV := generatorCoordinates4 1
    terms := 1
    radialRoot := generatorRadialRoots 0 14
  },
  {
    rectangle := generatorPartitionRectangles 104 11
    coordinateU := generatorCoordinates7 5
    coordinateV := generatorCoordinates2 0
    terms := 0
    radialRoot := generatorRadialRoots 0 15
  },
  {
    rectangle := generatorPartitionRectangles 104 12
    coordinateU := generatorCoordinates7 5
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 13
    coordinateU := generatorCoordinates7 4
    coordinateV := generatorCoordinates2 0
    terms := 1
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 14
    coordinateU := generatorCoordinates7 4
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 11
  },
  {
    rectangle := generatorPartitionRectangles 104 15
    coordinateU := generatorCoordinates6 3
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 20
  },
  {
    rectangle := generatorPartitionRectangles 104 16
    coordinateU := generatorCoordinates7 3
    coordinateV := generatorCoordinates2 4
    terms := 0
    radialRoot := generatorRadialRoots 0 19
  },
  {
    rectangle := generatorPartitionRectangles 104 17
    coordinateU := generatorCoordinates7 3
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 18
    coordinateU := generatorCoordinates7 2
    coordinateV := generatorCoordinates2 4
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 19
    coordinateU := generatorCoordinates7 2
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 15
  },
  {
    rectangle := generatorPartitionRectangles 104 20
    coordinateU := generatorCoordinates6 2
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 21
    coordinateU := generatorCoordinates6 2
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 22
    coordinateU := generatorCoordinates8 7
    coordinateV := generatorCoordinates4 4
    terms := 0
    radialRoot := generatorRadialRoots 0 16
  },
  {
    rectangle := generatorPartitionRectangles 104 23
    coordinateU := generatorCoordinates8 7
    coordinateV := generatorCoordinates4 3
    terms := 1
    radialRoot := generatorRadialRoots 0 15
  },
  {
    rectangle := generatorPartitionRectangles 104 24
    coordinateU := generatorCoordinates8 6
    coordinateV := generatorCoordinates4 4
    terms := 0
    radialRoot := generatorRadialRoots 0 15
  },
  {
    rectangle := generatorPartitionRectangles 104 25
    coordinateU := generatorCoordinates8 6
    coordinateV := generatorCoordinates4 3
    terms := 1
    radialRoot := generatorRadialRoots 0 14
  },
  {
    rectangle := generatorPartitionRectangles 104 26
    coordinateU := generatorCoordinates8 7
    coordinateV := generatorCoordinates4 2
    terms := 1
    radialRoot := generatorRadialRoots 0 14
  },
  {
    rectangle := generatorPartitionRectangles 104 27
    coordinateU := generatorCoordinates8 7
    coordinateV := generatorCoordinates4 1
    terms := 1
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 28
    coordinateU := generatorCoordinates8 6
    coordinateV := generatorCoordinates4 2
    terms := 1
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 29
    coordinateU := generatorCoordinates8 6
    coordinateV := generatorCoordinates4 1
    terms := 1
    radialRoot := generatorRadialRoots 0 12
  },
  {
    rectangle := generatorPartitionRectangles 104 30
    coordinateU := generatorCoordinates8 5
    coordinateV := generatorCoordinates4 4
    terms := 0
    radialRoot := generatorRadialRoots 0 14
  },
  {
    rectangle := generatorPartitionRectangles 104 31
    coordinateU := generatorCoordinates8 5
    coordinateV := generatorCoordinates4 3
    terms := 0
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 32
    coordinateU := generatorCoordinates8 4
    coordinateV := generatorCoordinates4 4
    terms := 0
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 33
    coordinateU := generatorCoordinates8 4
    coordinateV := generatorCoordinates4 3
    terms := 0
    radialRoot := generatorRadialRoots 0 12
  },
  {
    rectangle := generatorPartitionRectangles 104 34
    coordinateU := generatorCoordinates8 5
    coordinateV := generatorCoordinates4 2
    terms := 0
    radialRoot := generatorRadialRoots 0 12
  },
  {
    rectangle := generatorPartitionRectangles 104 35
    coordinateU := generatorCoordinates8 5
    coordinateV := generatorCoordinates4 1
    terms := 0
    radialRoot := generatorRadialRoots 0 11
  },
  {
    rectangle := generatorPartitionRectangles 104 36
    coordinateU := generatorCoordinates8 4
    coordinateV := generatorCoordinates4 2
    terms := 0
    radialRoot := generatorRadialRoots 0 11
  },
  {
    rectangle := generatorPartitionRectangles 104 37
    coordinateU := generatorCoordinates8 4
    coordinateV := generatorCoordinates4 1
    terms := 0
    radialRoot := generatorRadialRoots 0 10
  },
  {
    rectangle := generatorPartitionRectangles 104 38
    coordinateU := generatorCoordinates8 7
    coordinateV := generatorCoordinates4 0
    terms := 0
    radialRoot := generatorRadialRoots 0 12
  },
  {
    rectangle := generatorPartitionRectangles 104 39
    coordinateU := generatorCoordinates8 7
    coordinateV := generatorCoordinates3 7
    terms := 0
    radialRoot := generatorRadialRoots 0 11
  },
  {
    rectangle := generatorPartitionRectangles 104 40
    coordinateU := generatorCoordinates8 6
    coordinateV := generatorCoordinates4 0
    terms := 0
    radialRoot := generatorRadialRoots 0 11
  },
  {
    rectangle := generatorPartitionRectangles 104 41
    coordinateU := generatorCoordinates8 6
    coordinateV := generatorCoordinates3 7
    terms := 0
    radialRoot := generatorRadialRoots 0 10
  },
  {
    rectangle := generatorPartitionRectangles 104 42
    coordinateU := generatorCoordinates7 3
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 104 43
    coordinateU := generatorCoordinates7 2
    coordinateV := generatorCoordinates2 0
    terms := 1
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 104 44
    coordinateU := generatorCoordinates7 2
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 8
  },
  {
    rectangle := generatorPartitionRectangles 104 45
    coordinateU := generatorCoordinates7 1
    coordinateV := generatorCoordinates2 2
    terms := 0
    radialRoot := generatorRadialRoots 0 11
  },
  {
    rectangle := generatorPartitionRectangles 104 46
    coordinateU := generatorCoordinates7 1
    coordinateV := generatorCoordinates2 1
    terms := 0
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 104 47
    coordinateU := generatorCoordinates7 0
    coordinateV := generatorCoordinates2 2
    terms := 0
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 104 48
    coordinateU := generatorCoordinates7 0
    coordinateV := generatorCoordinates2 1
    terms := 0
    radialRoot := generatorRadialRoots 0 8
  },
  {
    rectangle := generatorPartitionRectangles 104 49
    coordinateU := generatorCoordinates7 1
    coordinateV := generatorCoordinates2 0
    terms := 0
    radialRoot := generatorRadialRoots 0 8
  },
  {
    rectangle := generatorPartitionRectangles 104 50
    coordinateU := generatorCoordinates7 1
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 7
  },
  {
    rectangle := generatorPartitionRectangles 104 51
    coordinateU := generatorCoordinates7 0
    coordinateV := generatorCoordinates2 0
    terms := 0
    radialRoot := generatorRadialRoots 0 7
  },
  {
    rectangle := generatorPartitionRectangles 104 52
    coordinateU := generatorCoordinates7 0
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 6
  },
  {
    rectangle := generatorPartitionRectangles 104 53
    coordinateU := generatorCoordinates5 3
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 22
  },
  {
    rectangle := generatorPartitionRectangles 104 54
    coordinateU := generatorCoordinates5 3
    coordinateV := generatorCoordinates0 5
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 55
    coordinateU := generatorCoordinates5 2
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 104 56
    coordinateU := generatorCoordinates5 2
    coordinateV := generatorCoordinates0 5
    terms := 0
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 104 57
    coordinateU := generatorCoordinates6 1
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 13
  },
  {
    rectangle := generatorPartitionRectangles 104 58
    coordinateU := generatorCoordinates6 1
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 104 59
    coordinateU := generatorCoordinates6 0
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 104 60
    coordinateU := generatorCoordinates6 0
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 7
  },
  {
    rectangle := generatorPartitionRectangles 104 61
    coordinateU := generatorCoordinates6 1
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 7
  },
  {
    rectangle := generatorPartitionRectangles 104 62
    coordinateU := generatorCoordinates6 1
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 5
  },
  {
    rectangle := generatorPartitionRectangles 104 63
    coordinateU := generatorCoordinates6 0
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 5
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks104_valid : ∀ i, (generatorLeafBlocks104 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks104 i).coordinateU.IsValid ∧
      (generatorLeafBlocks104 i).coordinateV.IsValid ∧
      (generatorLeafBlocks104 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates7_valid 6,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 15⟩
    · exact ⟨generatorCoordinates7_valid 5,
        generatorCoordinates2_valid 2, generatorRadialRoots_valid 0 19⟩
    · exact ⟨generatorCoordinates7_valid 5,
        generatorCoordinates2_valid 1, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates9_valid 1,
        generatorCoordinates4_valid 4, generatorRadialRoots_valid 0 18⟩
    · exact ⟨generatorCoordinates9_valid 1,
        generatorCoordinates4_valid 3, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates9_valid 0,
        generatorCoordinates4_valid 4, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates9_valid 0,
        generatorCoordinates4_valid 3, generatorRadialRoots_valid 0 16⟩
    · exact ⟨generatorCoordinates9_valid 1,
        generatorCoordinates4_valid 2, generatorRadialRoots_valid 0 16⟩
    · exact ⟨generatorCoordinates9_valid 1,
        generatorCoordinates4_valid 1, generatorRadialRoots_valid 0 15⟩
    · exact ⟨generatorCoordinates9_valid 0,
        generatorCoordinates4_valid 2, generatorRadialRoots_valid 0 15⟩
    · exact ⟨generatorCoordinates9_valid 0,
        generatorCoordinates4_valid 1, generatorRadialRoots_valid 0 14⟩
    · exact ⟨generatorCoordinates7_valid 5,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 0 15⟩
    · exact ⟨generatorCoordinates7_valid 5,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates7_valid 4,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates7_valid 4,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 11⟩
    · exact ⟨generatorCoordinates6_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 20⟩
    · exact ⟨generatorCoordinates7_valid 3,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 19⟩
    · exact ⟨generatorCoordinates7_valid 3,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates7_valid 2,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates7_valid 2,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 15⟩
    · exact ⟨generatorCoordinates6_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates6_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates8_valid 7,
        generatorCoordinates4_valid 4, generatorRadialRoots_valid 0 16⟩
    · exact ⟨generatorCoordinates8_valid 7,
        generatorCoordinates4_valid 3, generatorRadialRoots_valid 0 15⟩
    · exact ⟨generatorCoordinates8_valid 6,
        generatorCoordinates4_valid 4, generatorRadialRoots_valid 0 15⟩
    · exact ⟨generatorCoordinates8_valid 6,
        generatorCoordinates4_valid 3, generatorRadialRoots_valid 0 14⟩
    · exact ⟨generatorCoordinates8_valid 7,
        generatorCoordinates4_valid 2, generatorRadialRoots_valid 0 14⟩
    · exact ⟨generatorCoordinates8_valid 7,
        generatorCoordinates4_valid 1, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates8_valid 6,
        generatorCoordinates4_valid 2, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates8_valid 6,
        generatorCoordinates4_valid 1, generatorRadialRoots_valid 0 12⟩
    · exact ⟨generatorCoordinates8_valid 5,
        generatorCoordinates4_valid 4, generatorRadialRoots_valid 0 14⟩
    · exact ⟨generatorCoordinates8_valid 5,
        generatorCoordinates4_valid 3, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates8_valid 4,
        generatorCoordinates4_valid 4, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates8_valid 4,
        generatorCoordinates4_valid 3, generatorRadialRoots_valid 0 12⟩
    · exact ⟨generatorCoordinates8_valid 5,
        generatorCoordinates4_valid 2, generatorRadialRoots_valid 0 12⟩
    · exact ⟨generatorCoordinates8_valid 5,
        generatorCoordinates4_valid 1, generatorRadialRoots_valid 0 11⟩
    · exact ⟨generatorCoordinates8_valid 4,
        generatorCoordinates4_valid 2, generatorRadialRoots_valid 0 11⟩
    · exact ⟨generatorCoordinates8_valid 4,
        generatorCoordinates4_valid 1, generatorRadialRoots_valid 0 10⟩
    · exact ⟨generatorCoordinates8_valid 7,
        generatorCoordinates4_valid 0, generatorRadialRoots_valid 0 12⟩
    · exact ⟨generatorCoordinates8_valid 7,
        generatorCoordinates3_valid 7, generatorRadialRoots_valid 0 11⟩
    · exact ⟨generatorCoordinates8_valid 6,
        generatorCoordinates4_valid 0, generatorRadialRoots_valid 0 11⟩
    · exact ⟨generatorCoordinates8_valid 6,
        generatorCoordinates3_valid 7, generatorRadialRoots_valid 0 10⟩
    · exact ⟨generatorCoordinates7_valid 3,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates7_valid 2,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates7_valid 2,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 8⟩
    · exact ⟨generatorCoordinates7_valid 1,
        generatorCoordinates2_valid 2, generatorRadialRoots_valid 0 11⟩
    · exact ⟨generatorCoordinates7_valid 1,
        generatorCoordinates2_valid 1, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates7_valid 0,
        generatorCoordinates2_valid 2, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates7_valid 0,
        generatorCoordinates2_valid 1, generatorRadialRoots_valid 0 8⟩
    · exact ⟨generatorCoordinates7_valid 1,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 0 8⟩
    · exact ⟨generatorCoordinates7_valid 1,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 7⟩
    · exact ⟨generatorCoordinates7_valid 0,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 0 7⟩
    · exact ⟨generatorCoordinates7_valid 0,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 6⟩
    · exact ⟨generatorCoordinates5_valid 3,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 22⟩
    · exact ⟨generatorCoordinates5_valid 3,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates5_valid 2,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates5_valid 2,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates6_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 13⟩
    · exact ⟨generatorCoordinates6_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates6_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates6_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 7⟩
    · exact ⟨generatorCoordinates6_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 7⟩
    · exact ⟨generatorCoordinates6_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 5⟩
    · exact ⟨generatorCoordinates6_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 5⟩
  have hMeta : ∀ i, (generatorLeafBlocks104 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks104 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
