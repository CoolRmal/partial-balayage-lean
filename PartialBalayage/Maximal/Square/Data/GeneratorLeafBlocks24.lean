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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates62

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 24 of the recorded finite partition. -/
def generatorLeafBlocks24 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 24 0
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 24 1
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 24 2
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 24 3
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 24 4
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 24 5
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 24 6
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 24 7
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 24 8
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 24 9
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 24 10
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 24 11
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 24 12
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 24 13
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 24 14
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 24 15
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 24 16
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 24 17
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 24 18
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 24 19
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 24 20
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 24 21
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates5 2
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 24 22
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 24 23
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 24 24
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 24 25
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 24 26
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 24 27
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 24 28
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 24 29
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 24 30
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 24 31
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 24 32
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 24 33
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 24 34
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 24 35
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 24 36
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 24 37
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 24 38
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 24 39
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 24 40
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 24 41
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 24 42
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 24 43
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 24 44
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates0 5
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 24 45
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates1 2
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 24 46
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates1 1
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 24 47
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates1 2
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 24 48
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates1 1
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 24 49
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 24 50
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates1 2
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 24 51
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates1 1
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 24 52
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates1 2
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 24 53
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates1 1
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 24 54
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 24 55
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 24 56
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 24 57
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 24 58
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 24 59
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 24 60
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 24 61
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 24 62
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 24 63
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks24_valid : ∀ i, (generatorLeafBlocks24 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks24 i).coordinateU.IsValid ∧
      (generatorLeafBlocks24 i).coordinateV.IsValid ∧
      (generatorLeafBlocks24 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 10⟩
  have hMeta : ∀ i, (generatorLeafBlocks24 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks24 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
