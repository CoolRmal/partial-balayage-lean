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

/-- Actual source leaf candidates, block 100 of the recorded finite partition. -/
def generatorLeafBlocks100 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 100 0
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates1 4
    terms := 1
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 100 1
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates1 3
    terms := 1
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 100 2
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 100 3
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates1 3
    terms := 1
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 100 4
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 100 5
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 100 6
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 100 7
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 100 8
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 100 9
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 52
  },
  {
    rectangle := generatorPartitionRectangles 100 10
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 11
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 12
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 50
  },
  {
    rectangle := generatorPartitionRectangles 100 13
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 14
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 50
  },
  {
    rectangle := generatorPartitionRectangles 100 15
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 16
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 17
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 48
  },
  {
    rectangle := generatorPartitionRectangles 100 18
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 100 19
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 20
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 52
  },
  {
    rectangle := generatorPartitionRectangles 100 21
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 22
    coordinateU := generatorCoordinates17 0
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 23
    coordinateU := generatorCoordinates17 0
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 50
  },
  {
    rectangle := generatorPartitionRectangles 100 24
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 25
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 26
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 27
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 28
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 100 29
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 50
  },
  {
    rectangle := generatorPartitionRectangles 100 30
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 31
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 32
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 48
  },
  {
    rectangle := generatorPartitionRectangles 100 33
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates2 4
    terms := 1
    radialRoot := generatorRadialRoots 0 48
  },
  {
    rectangle := generatorPartitionRectangles 100 34
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 35
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates2 4
    terms := 1
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 36
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 46
  },
  {
    rectangle := generatorPartitionRectangles 100 37
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 48
  },
  {
    rectangle := generatorPartitionRectangles 100 38
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 39
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 40
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 46
  },
  {
    rectangle := generatorPartitionRectangles 100 41
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates2 4
    terms := 1
    radialRoot := generatorRadialRoots 0 46
  },
  {
    rectangle := generatorPartitionRectangles 100 42
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 100 43
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates2 4
    terms := 1
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 100 44
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 44
  },
  {
    rectangle := generatorPartitionRectangles 100 45
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 100 46
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 100 47
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 100 48
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 100 49
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 100 50
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 51
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 100 52
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 53
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 100 54
    coordinateU := generatorCoordinates16 3
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 48
  },
  {
    rectangle := generatorPartitionRectangles 100 55
    coordinateU := generatorCoordinates16 3
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 56
    coordinateU := generatorCoordinates16 2
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 57
    coordinateU := generatorCoordinates16 2
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 46
  },
  {
    rectangle := generatorPartitionRectangles 100 58
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 100 59
    coordinateU := generatorCoordinates16 1
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 46
  },
  {
    rectangle := generatorPartitionRectangles 100 60
    coordinateU := generatorCoordinates16 1
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 100 61
    coordinateU := generatorCoordinates16 0
    coordinateV := generatorCoordinates3 0
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 100 62
    coordinateU := generatorCoordinates16 0
    coordinateV := generatorCoordinates2 7
    terms := 0
    radialRoot := generatorRadialRoots 0 44
  },
  {
    rectangle := generatorPartitionRectangles 100 63
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 49
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks100_valid : ∀ i, (generatorLeafBlocks100 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks100 i).coordinateU.IsValid ∧
      (generatorLeafBlocks100 i).coordinateV.IsValid ∧
      (generatorLeafBlocks100 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 52⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 50⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 50⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 48⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 52⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates17_valid 0,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates17_valid 0,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 50⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 50⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 48⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 48⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 46⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 48⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 46⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 46⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 44⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates16_valid 3,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 48⟩
    · exact ⟨generatorCoordinates16_valid 3,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates16_valid 2,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates16_valid 2,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 46⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates16_valid 1,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 46⟩
    · exact ⟨generatorCoordinates16_valid 1,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates16_valid 0,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates16_valid 0,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 44⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 49⟩
  have hMeta : ∀ i, (generatorLeafBlocks100 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks100 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
