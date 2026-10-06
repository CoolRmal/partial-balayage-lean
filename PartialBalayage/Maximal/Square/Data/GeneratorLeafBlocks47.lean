/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates48
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 47 of the recorded finite partition. -/
def generatorLeafBlocks47 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 47 0
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 0
    terms := 12
    radialRoot := generatorRadialRoots 4 21
  },
  {
    rectangle := generatorPartitionRectangles 47 1
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates39 3
    terms := 8
    radialRoot := generatorRadialRoots 4 23
  },
  {
    rectangle := generatorPartitionRectangles 47 2
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates39 2
    terms := 12
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 47 3
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates39 3
    terms := 8
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 47 4
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates39 2
    terms := 12
    radialRoot := generatorRadialRoots 4 21
  },
  {
    rectangle := generatorPartitionRectangles 47 5
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates39 1
    terms := 12
    radialRoot := generatorRadialRoots 4 21
  },
  {
    rectangle := generatorPartitionRectangles 47 6
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates39 0
    terms := 20
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 47 7
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates39 1
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 47 8
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates39 0
    terms := 20
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 47 9
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates38 7
    terms := 12
    radialRoot := generatorRadialRoots 4 21
  },
  {
    rectangle := generatorPartitionRectangles 47 10
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates38 6
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 47 11
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates38 7
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 47 12
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates38 6
    terms := 12
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 47 13
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 47 14
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 15
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 16
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 17
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates38 7
    terms := 20
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 47 18
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates38 6
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 19
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates38 7
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 20
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates38 6
    terms := 20
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 21
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 22
    coordinateU := generatorCoordinates49 1
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 23
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 24
    coordinateU := generatorCoordinates49 0
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 47 25
    coordinateU := generatorCoordinates48 7
    coordinateV := generatorCoordinates39 3
    terms := 8
    radialRoot := generatorRadialRoots 4 21
  },
  {
    rectangle := generatorPartitionRectangles 47 26
    coordinateU := generatorCoordinates48 7
    coordinateV := generatorCoordinates39 2
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 47 27
    coordinateU := generatorCoordinates48 6
    coordinateV := generatorCoordinates39 3
    terms := 8
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 47 28
    coordinateU := generatorCoordinates48 6
    coordinateV := generatorCoordinates39 2
    terms := 8
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 47 29
    coordinateU := generatorCoordinates48 7
    coordinateV := generatorCoordinates39 1
    terms := 20
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 47 30
    coordinateU := generatorCoordinates50 1
    coordinateV := generatorCoordinates41 1
    terms := 20
    radialRoot := generatorRadialRoots 4 18
  },
  {
    rectangle := generatorPartitionRectangles 47 31
    coordinateU := generatorCoordinates50 1
    coordinateV := generatorCoordinates41 0
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 32
    coordinateU := generatorCoordinates50 0
    coordinateV := generatorCoordinates41 1
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 33
    coordinateU := generatorCoordinates50 0
    coordinateV := generatorCoordinates41 0
    terms := 20
    radialRoot := generatorRadialRoots 4 16
  },
  {
    rectangle := generatorPartitionRectangles 47 34
    coordinateU := generatorCoordinates48 6
    coordinateV := generatorCoordinates39 1
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 35
    coordinateU := generatorCoordinates49 7
    coordinateV := generatorCoordinates41 1
    terms := 12
    radialRoot := generatorRadialRoots 4 16
  },
  {
    rectangle := generatorPartitionRectangles 47 36
    coordinateU := generatorCoordinates49 7
    coordinateV := generatorCoordinates41 0
    terms := 20
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 37
    coordinateU := generatorCoordinates49 6
    coordinateV := generatorCoordinates41 1
    terms := 12
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 38
    coordinateU := generatorCoordinates49 6
    coordinateV := generatorCoordinates41 0
    terms := 20
    radialRoot := generatorRadialRoots 4 14
  },
  {
    rectangle := generatorPartitionRectangles 47 39
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates39 3
    terms := 5
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 47 40
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates39 2
    terms := 8
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 41
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates39 3
    terms := 4
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 47 42
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates39 2
    terms := 8
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 43
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates39 1
    terms := 12
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 44
    coordinateU := generatorCoordinates49 5
    coordinateV := generatorCoordinates41 1
    terms := 12
    radialRoot := generatorRadialRoots 4 14
  },
  {
    rectangle := generatorPartitionRectangles 47 45
    coordinateU := generatorCoordinates49 5
    coordinateV := generatorCoordinates41 0
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 46
    coordinateU := generatorCoordinates49 4
    coordinateV := generatorCoordinates41 1
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 47
    coordinateU := generatorCoordinates49 4
    coordinateV := generatorCoordinates41 0
    terms := 12
    radialRoot := generatorRadialRoots 4 12
  },
  {
    rectangle := generatorPartitionRectangles 47 48
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates39 1
    terms := 8
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 49
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates39 0
    terms := 12
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 47 50
    coordinateU := generatorCoordinates50 1
    coordinateV := generatorCoordinates40 7
    terms := 20
    radialRoot := generatorRadialRoots 4 16
  },
  {
    rectangle := generatorPartitionRectangles 47 51
    coordinateU := generatorCoordinates50 1
    coordinateV := generatorCoordinates40 6
    terms := 20
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 52
    coordinateU := generatorCoordinates50 0
    coordinateV := generatorCoordinates40 7
    terms := 20
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 47 53
    coordinateU := generatorCoordinates50 0
    coordinateV := generatorCoordinates40 6
    terms := 20
    radialRoot := generatorRadialRoots 4 14
  },
  {
    rectangle := generatorPartitionRectangles 47 54
    coordinateU := generatorCoordinates50 1
    coordinateV := generatorCoordinates40 5
    terms := 20
    radialRoot := generatorRadialRoots 4 14
  },
  {
    rectangle := generatorPartitionRectangles 47 55
    coordinateU := generatorCoordinates50 1
    coordinateV := generatorCoordinates40 4
    terms := 20
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 56
    coordinateU := generatorCoordinates50 0
    coordinateV := generatorCoordinates40 5
    terms := 20
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 57
    coordinateU := generatorCoordinates50 0
    coordinateV := generatorCoordinates40 4
    terms := 20
    radialRoot := generatorRadialRoots 4 12
  },
  {
    rectangle := generatorPartitionRectangles 47 58
    coordinateU := generatorCoordinates49 7
    coordinateV := generatorCoordinates40 7
    terms := 20
    radialRoot := generatorRadialRoots 4 14
  },
  {
    rectangle := generatorPartitionRectangles 47 59
    coordinateU := generatorCoordinates49 7
    coordinateV := generatorCoordinates40 6
    terms := 20
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 60
    coordinateU := generatorCoordinates49 6
    coordinateV := generatorCoordinates40 7
    terms := 20
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 47 61
    coordinateU := generatorCoordinates49 6
    coordinateV := generatorCoordinates40 6
    terms := 20
    radialRoot := generatorRadialRoots 4 12
  },
  {
    rectangle := generatorPartitionRectangles 47 62
    coordinateU := generatorCoordinates49 7
    coordinateV := generatorCoordinates40 5
    terms := 20
    radialRoot := generatorRadialRoots 4 12
  },
  {
    rectangle := generatorPartitionRectangles 47 63
    coordinateU := generatorCoordinates49 7
    coordinateV := generatorCoordinates40 4
    terms := 20
    radialRoot := generatorRadialRoots 4 11
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks47_valid : ∀ i, (generatorLeafBlocks47 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks47 i).coordinateU.IsValid ∧
      (generatorLeafBlocks47 i).coordinateV.IsValid ∧
      (generatorLeafBlocks47 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 0, generatorRadialRoots_valid 4 21⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 23⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 21⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 21⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates39_valid 0, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates39_valid 0, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates38_valid 7, generatorRadialRoots_valid 4 21⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates38_valid 7, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates38_valid 7, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates38_valid 7, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates49_valid 1,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 0,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates48_valid 7,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 21⟩
    · exact ⟨generatorCoordinates48_valid 7,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates48_valid 6,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates48_valid 6,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates48_valid 7,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates50_valid 1,
        generatorCoordinates41_valid 1, generatorRadialRoots_valid 4 18⟩
    · exact ⟨generatorCoordinates50_valid 1,
        generatorCoordinates41_valid 0, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates50_valid 0,
        generatorCoordinates41_valid 1, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates50_valid 0,
        generatorCoordinates41_valid 0, generatorRadialRoots_valid 4 16⟩
    · exact ⟨generatorCoordinates48_valid 6,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates49_valid 7,
        generatorCoordinates41_valid 1, generatorRadialRoots_valid 4 16⟩
    · exact ⟨generatorCoordinates49_valid 7,
        generatorCoordinates41_valid 0, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates49_valid 6,
        generatorCoordinates41_valid 1, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates49_valid 6,
        generatorCoordinates41_valid 0, generatorRadialRoots_valid 4 14⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates49_valid 5,
        generatorCoordinates41_valid 1, generatorRadialRoots_valid 4 14⟩
    · exact ⟨generatorCoordinates49_valid 5,
        generatorCoordinates41_valid 0, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 4,
        generatorCoordinates41_valid 1, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 4,
        generatorCoordinates41_valid 0, generatorRadialRoots_valid 4 12⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates39_valid 0, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates50_valid 1,
        generatorCoordinates40_valid 7, generatorRadialRoots_valid 4 16⟩
    · exact ⟨generatorCoordinates50_valid 1,
        generatorCoordinates40_valid 6, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates50_valid 0,
        generatorCoordinates40_valid 7, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates50_valid 0,
        generatorCoordinates40_valid 6, generatorRadialRoots_valid 4 14⟩
    · exact ⟨generatorCoordinates50_valid 1,
        generatorCoordinates40_valid 5, generatorRadialRoots_valid 4 14⟩
    · exact ⟨generatorCoordinates50_valid 1,
        generatorCoordinates40_valid 4, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates50_valid 0,
        generatorCoordinates40_valid 5, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates50_valid 0,
        generatorCoordinates40_valid 4, generatorRadialRoots_valid 4 12⟩
    · exact ⟨generatorCoordinates49_valid 7,
        generatorCoordinates40_valid 7, generatorRadialRoots_valid 4 14⟩
    · exact ⟨generatorCoordinates49_valid 7,
        generatorCoordinates40_valid 6, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 6,
        generatorCoordinates40_valid 7, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 6,
        generatorCoordinates40_valid 6, generatorRadialRoots_valid 4 12⟩
    · exact ⟨generatorCoordinates49_valid 7,
        generatorCoordinates40_valid 5, generatorRadialRoots_valid 4 12⟩
    · exact ⟨generatorCoordinates49_valid 7,
        generatorCoordinates40_valid 4, generatorRadialRoots_valid 4 11⟩
  have hMeta : ∀ i, (generatorLeafBlocks47 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks47 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
