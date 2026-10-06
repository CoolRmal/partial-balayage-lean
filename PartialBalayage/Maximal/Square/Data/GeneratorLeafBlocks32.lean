/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates56
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates58

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 32 of the recorded finite partition. -/
def generatorLeafBlocks32 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 32 0
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates41 5
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 1
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates41 6
    terms := 3
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 2
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates41 5
    terms := 30
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 3
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates38 3
    terms := 12
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 32 4
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates38 2
    terms := 12
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 32 5
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates38 3
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 32 6
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates38 2
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 32 7
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates38 1
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 32 8
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates38 0
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 9
    coordinateU := generatorCoordinates58 5
    coordinateV := generatorCoordinates39 7
    terms := 12
    radialRoot := generatorRadialRoots 5 3
  },
  {
    rectangle := generatorPartitionRectangles 32 10
    coordinateU := generatorCoordinates58 5
    coordinateV := generatorCoordinates39 6
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 11
    coordinateU := generatorCoordinates58 4
    coordinateV := generatorCoordinates39 7
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 12
    coordinateU := generatorCoordinates58 4
    coordinateV := generatorCoordinates39 6
    terms := 20
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 32 13
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates38 0
    terms := 30
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 32 14
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates38 3
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 32 15
    coordinateU := generatorCoordinates58 3
    coordinateV := generatorCoordinates40 1
    terms := 20
    radialRoot := generatorRadialRoots 5 3
  },
  {
    rectangle := generatorPartitionRectangles 32 16
    coordinateU := generatorCoordinates58 3
    coordinateV := generatorCoordinates40 0
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 17
    coordinateU := generatorCoordinates58 2
    coordinateV := generatorCoordinates40 1
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 18
    coordinateU := generatorCoordinates58 2
    coordinateV := generatorCoordinates40 0
    terms := 20
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 32 19
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates38 3
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 32 20
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates38 2
    terms := 50
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 32 21
    coordinateU := generatorCoordinates58 3
    coordinateV := generatorCoordinates39 7
    terms := 20
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 32 22
    coordinateU := generatorCoordinates58 3
    coordinateV := generatorCoordinates39 6
    terms := 30
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 32 23
    coordinateU := generatorCoordinates58 2
    coordinateV := generatorCoordinates39 7
    terms := 30
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 32 24
    coordinateU := generatorCoordinates58 2
    coordinateV := generatorCoordinates39 6
    terms := 30
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 32 25
    coordinateU := generatorCoordinates58 3
    coordinateV := generatorCoordinates39 5
    terms := 30
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 32 26
    coordinateU := generatorCoordinates58 3
    coordinateV := generatorCoordinates39 4
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 27
    coordinateU := generatorCoordinates58 2
    coordinateV := generatorCoordinates39 5
    terms := 30
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 28
    coordinateU := generatorCoordinates58 2
    coordinateV := generatorCoordinates39 4
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 32 29
    coordinateU := generatorCoordinates58 1
    coordinateV := generatorCoordinates39 7
    terms := 30
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 32 30
    coordinateU := generatorCoordinates58 1
    coordinateV := generatorCoordinates39 6
    terms := 50
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 31
    coordinateU := generatorCoordinates58 0
    coordinateV := generatorCoordinates39 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 32
    coordinateU := generatorCoordinates58 0
    coordinateV := generatorCoordinates39 6
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 32 33
    coordinateU := generatorCoordinates58 1
    coordinateV := generatorCoordinates39 5
    terms := 30
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 32 34
    coordinateU := generatorCoordinates58 1
    coordinateV := generatorCoordinates39 4
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 32 35
    coordinateU := generatorCoordinates58 0
    coordinateV := generatorCoordinates39 5
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 32 36
    coordinateU := generatorCoordinates58 0
    coordinateV := generatorCoordinates39 4
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 32 37
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates37 7
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 32 38
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates37 6
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 39
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates37 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 40
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates37 6
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 32 41
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates37 0
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 32 42
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates37 7
    terms := 50
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 32 43
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates37 6
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 32 44
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates37 7
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 32 45
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates37 6
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 32 46
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates37 0
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 32 47
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates38 3
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 32 48
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates38 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 49
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates38 3
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 32 50
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates38 2
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 32 51
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates38 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 32 52
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates38 0
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 32 53
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates38 1
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 32 54
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates38 0
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 32 55
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates38 3
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 32 56
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates38 2
    terms := 8
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 32 57
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates38 3
    terms := 5
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 32 58
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates38 2
    terms := 5
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 32 59
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates38 1
    terms := 8
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 32 60
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates38 0
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 32 61
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates38 1
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 32 62
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates38 0
    terms := 8
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 32 63
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates37 7
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks32_valid : ∀ i, (generatorLeafBlocks32 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks32 i).coordinateU.IsValid ∧
      (generatorLeafBlocks32 i).coordinateV.IsValid ∧
      (generatorLeafBlocks32 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates58_valid 5,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 5 3⟩
    · exact ⟨generatorCoordinates58_valid 5,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates58_valid 4,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates58_valid 4,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates58_valid 3,
        generatorCoordinates40_valid 1, generatorRadialRoots_valid 5 3⟩
    · exact ⟨generatorCoordinates58_valid 3,
        generatorCoordinates40_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates58_valid 2,
        generatorCoordinates40_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates58_valid 2,
        generatorCoordinates40_valid 0, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates58_valid 3,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates58_valid 3,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates58_valid 2,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates58_valid 2,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates58_valid 3,
        generatorCoordinates39_valid 5, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates58_valid 3,
        generatorCoordinates39_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates58_valid 2,
        generatorCoordinates39_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates58_valid 2,
        generatorCoordinates39_valid 4, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates58_valid 1,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates58_valid 1,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates58_valid 0,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates58_valid 0,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates58_valid 1,
        generatorCoordinates39_valid 5, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates58_valid 1,
        generatorCoordinates39_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates58_valid 0,
        generatorCoordinates39_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates58_valid 0,
        generatorCoordinates39_valid 4, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 54⟩
  have hMeta : ∀ i, (generatorLeafBlocks32 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks32 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
