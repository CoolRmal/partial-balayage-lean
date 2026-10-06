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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 80 of the recorded finite partition. -/
def generatorLeafBlocks80 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 80 0
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 80 1
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 80 2
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 80 3
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 80 4
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 80 5
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 80 6
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 80 7
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 80 8
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 80 9
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 80 10
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 80 11
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 80 12
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 80 13
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 80 14
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 80 15
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 16
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 17
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 80 18
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 80 19
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 20
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 21
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 80 22
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 80 23
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 80 24
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 80 25
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 80 26
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 80 27
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 80 28
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 80 29
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 80 30
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 80 31
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 32
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 33
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 80 34
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 80 35
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 36
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 80 37
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 80 38
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 80 39
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 80 40
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 80 41
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 80 42
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 80 43
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 80 44
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 80 45
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 80 46
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 80 47
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 80 48
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 80 49
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 80 50
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 80 51
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 80 52
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 80 53
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 80 54
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 80 55
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 80 56
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 80 57
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 80 58
    coordinateU := generatorCoordinates25 6
    coordinateV := generatorCoordinates25 6
    terms := 3
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 80 59
    coordinateU := generatorCoordinates25 6
    coordinateV := generatorCoordinates25 5
    terms := 3
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 80 60
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates25 6
    terms := 3
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 80 61
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates25 5
    terms := 3
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 80 62
    coordinateU := generatorCoordinates25 6
    coordinateV := generatorCoordinates25 4
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 80 63
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks80_valid : ∀ i, (generatorLeafBlocks80 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks80 i).coordinateU.IsValid ∧
      (generatorLeafBlocks80 i).coordinateV.IsValid ∧
      (generatorLeafBlocks80 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates25_valid 6,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates25_valid 6,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates25_valid 6,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 44⟩
  have hMeta : ∀ i, (generatorLeafBlocks80 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks80 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
