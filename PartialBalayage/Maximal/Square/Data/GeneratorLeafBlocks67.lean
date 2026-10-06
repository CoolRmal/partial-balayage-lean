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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 67 of the recorded finite partition. -/
def generatorLeafBlocks67 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 67 0
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 67 1
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates5 5
    terms := 5
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 67 2
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates5 4
    terms := 5
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 67 3
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates5 5
    terms := 5
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 67 4
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates5 4
    terms := 5
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 67 5
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates5 3
    terms := 4
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 67 6
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 67 7
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 67 8
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 67 9
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 67 10
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates5 3
    terms := 4
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 67 11
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 67 12
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 67 13
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 67 14
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 67 15
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates5 5
    terms := 5
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 67 16
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 67 17
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 67 18
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 67 19
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 67 20
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 67 21
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 67 22
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates5 3
    terms := 4
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 67 23
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 67 24
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 67 25
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 67 26
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 67 27
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates5 3
    terms := 4
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 67 28
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 67 29
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 30
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates5 7
    terms := 2
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 31
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates5 6
    terms := 2
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 67 32
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 67 33
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 67 34
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 67 35
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 67 36
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 67 37
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 67 38
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 67 39
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 67 40
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 67 41
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 67 42
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 67 43
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 67 44
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 67 45
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 46
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 47
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 67 48
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 67 49
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 50
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 51
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 67 52
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 67 53
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 67 54
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 67 55
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 67 56
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 67 57
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 67 58
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 67 59
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 60
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 67 61
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 67 62
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 67 63
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 5
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks67_valid : ∀ i, (generatorLeafBlocks67 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks67 i).coordinateU.IsValid ∧
      (generatorLeafBlocks67 i).coordinateV.IsValid ∧
      (generatorLeafBlocks67 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 5⟩
  have hMeta : ∀ i, (generatorLeafBlocks67 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks67 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
