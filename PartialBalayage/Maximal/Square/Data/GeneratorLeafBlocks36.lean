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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates56

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 36 of the recorded finite partition. -/
def generatorLeafBlocks36 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 36 0
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 36 1
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 36 2
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 36 3
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 36 4
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 36 5
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 36 6
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 36 7
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 36 8
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 36 9
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 36 10
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 36 11
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 36 12
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 36 13
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 36 14
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 36 15
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 36 16
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 36 17
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 36 18
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 36 19
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 36 20
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 36 21
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 36 22
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 36 23
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 36 24
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 36 25
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 36 26
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 36 27
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 36 28
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 36 29
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 36 30
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 36 31
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 36 32
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 36 33
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 36 34
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 36 35
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 36 36
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 36 37
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 36 38
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 36 39
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 36 40
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 36 41
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 36 42
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 36 43
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 36 44
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 36 45
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 36 46
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 36 47
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 36 48
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 36 49
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 36 50
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 36 51
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 36 52
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 36 53
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 36 54
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 36 55
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 36 56
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 36 57
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 36 58
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 36 59
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 36 60
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 36 61
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 36 62
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 36 63
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks36_valid : ∀ i, (generatorLeafBlocks36 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks36 i).coordinateU.IsValid ∧
      (generatorLeafBlocks36 i).coordinateV.IsValid ∧
      (generatorLeafBlocks36 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 55⟩
  have hMeta : ∀ i, (generatorLeafBlocks36 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks36 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
