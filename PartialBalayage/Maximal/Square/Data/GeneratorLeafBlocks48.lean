/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates48

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 48 of the recorded finite partition. -/
def generatorLeafBlocks48 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 48 0
    coordinateU := generatorCoordinates49 6
    coordinateV := generatorCoordinates40 5
    terms := 20
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 48 1
    coordinateU := generatorCoordinates49 6
    coordinateV := generatorCoordinates40 4
    terms := 20
    radialRoot := generatorRadialRoots 4 10
  },
  {
    rectangle := generatorPartitionRectangles 48 2
    coordinateU := generatorCoordinates48 7
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 48 3
    coordinateU := generatorCoordinates48 7
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 4
    coordinateU := generatorCoordinates48 6
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 5
    coordinateU := generatorCoordinates48 6
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 48 6
    coordinateU := generatorCoordinates49 5
    coordinateV := generatorCoordinates40 7
    terms := 20
    radialRoot := generatorRadialRoots 4 12
  },
  {
    rectangle := generatorPartitionRectangles 48 7
    coordinateU := generatorCoordinates49 5
    coordinateV := generatorCoordinates40 6
    terms := 20
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 48 8
    coordinateU := generatorCoordinates49 4
    coordinateV := generatorCoordinates40 7
    terms := 12
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 48 9
    coordinateU := generatorCoordinates49 4
    coordinateV := generatorCoordinates40 6
    terms := 12
    radialRoot := generatorRadialRoots 4 10
  },
  {
    rectangle := generatorPartitionRectangles 48 10
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates38 6
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 11
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates38 7
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 12
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates38 6
    terms := 12
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 48 13
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 48 14
    coordinateU := generatorCoordinates48 5
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 15
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 16
    coordinateU := generatorCoordinates48 4
    coordinateV := generatorCoordinates38 4
    terms := 8
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 48 17
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates38 3
    terms := 0
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 48 18
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates38 2
    terms := 0
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 48 19
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates38 3
    terms := 0
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 48 20
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates38 2
    terms := 0
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 48 21
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates38 1
    terms := 1
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 48 22
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates38 0
    terms := 3
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 48 23
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates38 1
    terms := 0
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 48 24
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates38 0
    terms := 1
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 48 25
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates37 3
    terms := 3
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 48 26
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates38 1
    terms := 0
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 48 27
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates38 0
    terms := 1
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 28
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates38 1
    terms := 0
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 29
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates38 0
    terms := 0
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 30
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates37 7
    terms := 8
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 48 31
    coordinateU := generatorCoordinates48 3
    coordinateV := generatorCoordinates39 1
    terms := 8
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 48 32
    coordinateU := generatorCoordinates48 3
    coordinateV := generatorCoordinates39 0
    terms := 8
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 33
    coordinateU := generatorCoordinates48 2
    coordinateV := generatorCoordinates39 1
    terms := 5
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 34
    coordinateU := generatorCoordinates48 2
    coordinateV := generatorCoordinates39 0
    terms := 8
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 48 35
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates37 7
    terms := 4
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 36
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates37 6
    terms := 8
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 37
    coordinateU := generatorCoordinates48 3
    coordinateV := generatorCoordinates38 7
    terms := 12
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 48 38
    coordinateU := generatorCoordinates48 3
    coordinateV := generatorCoordinates38 6
    terms := 8
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 39
    coordinateU := generatorCoordinates48 2
    coordinateV := generatorCoordinates38 7
    terms := 8
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 40
    coordinateU := generatorCoordinates48 2
    coordinateV := generatorCoordinates38 6
    terms := 8
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 48 41
    coordinateU := generatorCoordinates48 3
    coordinateV := generatorCoordinates38 5
    terms := 8
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 48 42
    coordinateU := generatorCoordinates48 3
    coordinateV := generatorCoordinates38 4
    terms := 8
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 48 43
    coordinateU := generatorCoordinates48 2
    coordinateV := generatorCoordinates38 5
    terms := 8
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 48 44
    coordinateU := generatorCoordinates48 2
    coordinateV := generatorCoordinates38 4
    terms := 8
    radialRoot := generatorRadialRoots 4 4
  },
  {
    rectangle := generatorPartitionRectangles 48 45
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates37 5
    terms := 8
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 48 46
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates37 4
    terms := 8
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 48 47
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates37 7
    terms := 2
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 48
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates37 6
    terms := 3
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 48 49
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates37 7
    terms := 1
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 48 50
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates37 6
    terms := 2
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 48 51
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates37 5
    terms := 4
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 48 52
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates37 4
    terms := 5
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 48 53
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates37 5
    terms := 2
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 48 54
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates37 4
    terms := 3
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 48 55
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates36 4
    terms := 12
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 48 56
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates36 3
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 48 57
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates36 4
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 48 58
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates36 3
    terms := 12
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 48 59
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates34 3
    terms := 30
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 60
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates34 4
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 48 61
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 48 62
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates36 0
    terms := 12
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 48 63
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 7
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks48_valid : ∀ i, (generatorLeafBlocks48 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks48 i).coordinateU.IsValid ∧
      (generatorLeafBlocks48 i).coordinateV.IsValid ∧
      (generatorLeafBlocks48 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates49_valid 6,
        generatorCoordinates40_valid 5, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates49_valid 6,
        generatorCoordinates40_valid 4, generatorRadialRoots_valid 4 10⟩
    · exact ⟨generatorCoordinates48_valid 7,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates48_valid 7,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates48_valid 6,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates48_valid 6,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates49_valid 5,
        generatorCoordinates40_valid 7, generatorRadialRoots_valid 4 12⟩
    · exact ⟨generatorCoordinates49_valid 5,
        generatorCoordinates40_valid 6, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates49_valid 4,
        generatorCoordinates40_valid 7, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates49_valid 4,
        generatorCoordinates40_valid 6, generatorRadialRoots_valid 4 10⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates38_valid 7, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates48_valid 5,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates48_valid 4,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates48_valid 3,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates48_valid 3,
        generatorCoordinates39_valid 0, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates48_valid 2,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates48_valid 2,
        generatorCoordinates39_valid 0, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates48_valid 3,
        generatorCoordinates38_valid 7, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates48_valid 3,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates48_valid 2,
        generatorCoordinates38_valid 7, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates48_valid 2,
        generatorCoordinates38_valid 6, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates48_valid 3,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates48_valid 3,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates48_valid 2,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates48_valid 2,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 4⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 7⟩
  have hMeta : ∀ i, (generatorLeafBlocks48 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks48 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
