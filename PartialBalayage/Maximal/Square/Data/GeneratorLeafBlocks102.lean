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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates12
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 102 of the recorded finite partition. -/
def generatorLeafBlocks102 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 102 0
    coordinateU := generatorCoordinates12 5
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 102 1
    coordinateU := generatorCoordinates12 5
    coordinateV := generatorCoordinates3 1
    terms := 0
    radialRoot := generatorRadialRoots 0 40
  },
  {
    rectangle := generatorPartitionRectangles 102 2
    coordinateU := generatorCoordinates12 6
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 40
  },
  {
    rectangle := generatorPartitionRectangles 102 3
    coordinateU := generatorCoordinates12 6
    coordinateV := generatorCoordinates2 7
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 102 4
    coordinateU := generatorCoordinates12 5
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 102 5
    coordinateU := generatorCoordinates12 5
    coordinateV := generatorCoordinates2 7
    terms := 0
    radialRoot := generatorRadialRoots 0 38
  },
  {
    rectangle := generatorPartitionRectangles 102 6
    coordinateU := generatorCoordinates12 4
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 40
  },
  {
    rectangle := generatorPartitionRectangles 102 7
    coordinateU := generatorCoordinates12 4
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 102 8
    coordinateU := generatorCoordinates12 3
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 102 9
    coordinateU := generatorCoordinates12 3
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 0 38
  },
  {
    rectangle := generatorPartitionRectangles 102 10
    coordinateU := generatorCoordinates12 4
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 38
  },
  {
    rectangle := generatorPartitionRectangles 102 11
    coordinateU := generatorCoordinates12 4
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 12
    coordinateU := generatorCoordinates12 3
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 13
    coordinateU := generatorCoordinates12 3
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 34
  },
  {
    rectangle := generatorPartitionRectangles 102 14
    coordinateU := generatorCoordinates10 6
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 102 15
    coordinateU := generatorCoordinates12 2
    coordinateV := generatorCoordinates3 4
    terms := 0
    radialRoot := generatorRadialRoots 0 40
  },
  {
    rectangle := generatorPartitionRectangles 102 16
    coordinateU := generatorCoordinates12 2
    coordinateV := generatorCoordinates3 3
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 102 17
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates3 4
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 102 18
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates3 3
    terms := 0
    radialRoot := generatorRadialRoots 0 38
  },
  {
    rectangle := generatorPartitionRectangles 102 19
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 102 20
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 21
    coordinateU := generatorCoordinates12 2
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 38
  },
  {
    rectangle := generatorPartitionRectangles 102 22
    coordinateU := generatorCoordinates13 4
    coordinateV := generatorCoordinates4 6
    terms := 0
    radialRoot := generatorRadialRoots 0 37
  },
  {
    rectangle := generatorPartitionRectangles 102 23
    coordinateU := generatorCoordinates13 4
    coordinateV := generatorCoordinates4 5
    terms := 1
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 24
    coordinateU := generatorCoordinates13 3
    coordinateV := generatorCoordinates4 6
    terms := 0
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 25
    coordinateU := generatorCoordinates13 3
    coordinateV := generatorCoordinates4 5
    terms := 1
    radialRoot := generatorRadialRoots 0 35
  },
  {
    rectangle := generatorPartitionRectangles 102 26
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 27
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 0 34
  },
  {
    rectangle := generatorPartitionRectangles 102 28
    coordinateU := generatorCoordinates12 2
    coordinateV := generatorCoordinates3 0
    terms := 3
    radialRoot := generatorRadialRoots 0 34
  },
  {
    rectangle := generatorPartitionRectangles 102 29
    coordinateU := generatorCoordinates12 2
    coordinateV := generatorCoordinates2 7
    terms := 2
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 102 30
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 102 31
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 32
  },
  {
    rectangle := generatorPartitionRectangles 102 32
    coordinateU := generatorCoordinates12 0
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 34
  },
  {
    rectangle := generatorPartitionRectangles 102 33
    coordinateU := generatorCoordinates12 0
    coordinateV := generatorCoordinates3 1
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 102 34
    coordinateU := generatorCoordinates11 7
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 102 35
    coordinateU := generatorCoordinates11 7
    coordinateV := generatorCoordinates3 1
    terms := 0
    radialRoot := generatorRadialRoots 0 32
  },
  {
    rectangle := generatorPartitionRectangles 102 36
    coordinateU := generatorCoordinates12 0
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 32
  },
  {
    rectangle := generatorPartitionRectangles 102 37
    coordinateU := generatorCoordinates12 0
    coordinateV := generatorCoordinates2 7
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 102 38
    coordinateU := generatorCoordinates11 7
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 102 39
    coordinateU := generatorCoordinates11 7
    coordinateV := generatorCoordinates2 7
    terms := 0
    radialRoot := generatorRadialRoots 0 30
  },
  {
    rectangle := generatorPartitionRectangles 102 40
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 41
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 102 42
    coordinateU := generatorCoordinates12 4
    coordinateV := generatorCoordinates2 6
    terms := 0
    radialRoot := generatorRadialRoots 0 34
  },
  {
    rectangle := generatorPartitionRectangles 102 43
    coordinateU := generatorCoordinates12 4
    coordinateV := generatorCoordinates2 5
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 102 44
    coordinateU := generatorCoordinates12 3
    coordinateV := generatorCoordinates2 6
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 102 45
    coordinateU := generatorCoordinates12 3
    coordinateV := generatorCoordinates2 5
    terms := 0
    radialRoot := generatorRadialRoots 0 32
  },
  {
    rectangle := generatorPartitionRectangles 102 46
    coordinateU := generatorCoordinates10 7
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 102 47
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 102 48
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 102 49
    coordinateU := generatorCoordinates10 7
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 102 50
    coordinateU := generatorCoordinates10 7
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 28
  },
  {
    rectangle := generatorPartitionRectangles 102 51
    coordinateU := generatorCoordinates12 2
    coordinateV := generatorCoordinates2 6
    terms := 0
    radialRoot := generatorRadialRoots 0 32
  },
  {
    rectangle := generatorPartitionRectangles 102 52
    coordinateU := generatorCoordinates12 2
    coordinateV := generatorCoordinates2 5
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 102 53
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates2 6
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 102 54
    coordinateU := generatorCoordinates12 1
    coordinateV := generatorCoordinates2 5
    terms := 0
    radialRoot := generatorRadialRoots 0 30
  },
  {
    rectangle := generatorPartitionRectangles 102 55
    coordinateU := generatorCoordinates10 6
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 102 56
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 102 57
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 28
  },
  {
    rectangle := generatorPartitionRectangles 102 58
    coordinateU := generatorCoordinates10 6
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 28
  },
  {
    rectangle := generatorPartitionRectangles 102 59
    coordinateU := generatorCoordinates10 6
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 102 60
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 102 61
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 26
  },
  {
    rectangle := generatorPartitionRectangles 102 62
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 102 63
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks102_valid : ∀ i, (generatorLeafBlocks102 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks102 i).coordinateU.IsValid ∧
      (generatorLeafBlocks102 i).coordinateV.IsValid ∧
      (generatorLeafBlocks102 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates12_valid 5,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates12_valid 5,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 40⟩
    · exact ⟨generatorCoordinates12_valid 6,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 40⟩
    · exact ⟨generatorCoordinates12_valid 6,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates12_valid 5,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates12_valid 5,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 38⟩
    · exact ⟨generatorCoordinates12_valid 4,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 40⟩
    · exact ⟨generatorCoordinates12_valid 4,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates12_valid 3,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates12_valid 3,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 38⟩
    · exact ⟨generatorCoordinates12_valid 4,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 38⟩
    · exact ⟨generatorCoordinates12_valid 4,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates12_valid 3,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates12_valid 3,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 34⟩
    · exact ⟨generatorCoordinates10_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates12_valid 2,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 0 40⟩
    · exact ⟨generatorCoordinates12_valid 2,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates3_valid 4, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates3_valid 3, generatorRadialRoots_valid 0 38⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates12_valid 2,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 38⟩
    · exact ⟨generatorCoordinates13_valid 4,
        generatorCoordinates4_valid 6, generatorRadialRoots_valid 0 37⟩
    · exact ⟨generatorCoordinates13_valid 4,
        generatorCoordinates4_valid 5, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates13_valid 3,
        generatorCoordinates4_valid 6, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates13_valid 3,
        generatorCoordinates4_valid 5, generatorRadialRoots_valid 0 35⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 34⟩
    · exact ⟨generatorCoordinates12_valid 2,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 34⟩
    · exact ⟨generatorCoordinates12_valid 2,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 32⟩
    · exact ⟨generatorCoordinates12_valid 0,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 34⟩
    · exact ⟨generatorCoordinates12_valid 0,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates11_valid 7,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates11_valid 7,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 32⟩
    · exact ⟨generatorCoordinates12_valid 0,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 32⟩
    · exact ⟨generatorCoordinates12_valid 0,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates11_valid 7,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates11_valid 7,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 30⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates12_valid 4,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 34⟩
    · exact ⟨generatorCoordinates12_valid 4,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates12_valid 3,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates12_valid 3,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 32⟩
    · exact ⟨generatorCoordinates10_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 28⟩
    · exact ⟨generatorCoordinates12_valid 2,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 32⟩
    · exact ⟨generatorCoordinates12_valid 2,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates12_valid 1,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 30⟩
    · exact ⟨generatorCoordinates10_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 28⟩
    · exact ⟨generatorCoordinates10_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 28⟩
    · exact ⟨generatorCoordinates10_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 26⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 33⟩
  have hMeta : ∀ i, (generatorLeafBlocks102 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks102 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
