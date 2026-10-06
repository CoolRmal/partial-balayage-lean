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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 62 of the recorded finite partition. -/
def generatorLeafBlocks62 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 62 0
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 62 1
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 62 2
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 62 3
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 62 4
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 62 5
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 62 6
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 62 7
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 62 8
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 62 9
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 62 10
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 62 11
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 62 12
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 62 13
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 62 14
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 62 15
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 62 16
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 62 17
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 62 18
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 62 19
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 62 20
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 62 21
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 62 22
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 62 23
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 62 24
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 62 25
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 62 26
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 62 27
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 62 28
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 62 29
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 62 30
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 62 31
    coordinateU := generatorCoordinates36 7
    coordinateV := generatorCoordinates36 7
    terms := 0
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 62 32
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 62 33
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates37 0
    terms := 0
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 62 34
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 62 35
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates37 0
    terms := 1
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 62 36
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates37 3
    terms := 0
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 62 37
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates37 2
    terms := 0
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 62 38
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates37 3
    terms := 0
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 62 39
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates37 2
    terms := 1
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 62 40
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 62 41
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates37 0
    terms := 4
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 62 42
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates37 1
    terms := 4
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 62 43
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates37 5
    terms := 0
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 62 44
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates37 4
    terms := 1
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 62 45
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates37 5
    terms := 1
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 62 46
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates37 4
    terms := 3
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 62 47
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates34 4
    terms := 0
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 62 48
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 62 49
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates34 4
    terms := 0
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 62 50
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 62 51
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates34 2
    terms := 1
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 62 52
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates34 1
    terms := 2
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 62 53
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates34 2
    terms := 1
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 62 54
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates34 1
    terms := 2
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 62 55
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates34 4
    terms := 0
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 62 56
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 62 57
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates34 4
    terms := 0
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 62 58
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 62 59
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates33 3
    terms := 5
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 62 60
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates34 0
    terms := 3
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 62 61
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates33 7
    terms := 4
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 62 62
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates34 0
    terms := 3
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 62 63
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates33 7
    terms := 4
    radialRoot := generatorRadialRoots 3 34
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks62_valid : ∀ i, (generatorLeafBlocks62 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks62 i).coordinateU.IsValid ∧
      (generatorLeafBlocks62 i).coordinateV.IsValid ∧
      (generatorLeafBlocks62 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates36_valid 7,
        generatorCoordinates36_valid 7, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 34⟩
  have hMeta : ∀ i, (generatorLeafBlocks62 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks62 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
