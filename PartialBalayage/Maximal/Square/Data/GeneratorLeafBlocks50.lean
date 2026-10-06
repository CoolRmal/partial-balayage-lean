/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
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

/-- Actual source leaf candidates, block 50 of the recorded finite partition. -/
def generatorLeafBlocks50 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 50 0
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates34 2
    terms := 8
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 50 1
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates34 1
    terms := 20
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 50 2
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates34 0
    terms := 20
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 50 3
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 50 4
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates34 0
    terms := 20
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 50 5
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 50 6
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 50 7
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 8
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 9
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 50 10
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 50 11
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 12
    coordinateU := generatorCoordinates48 1
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 55
  },
  {
    rectangle := generatorPartitionRectangles 50 13
    coordinateU := generatorCoordinates48 1
    coordinateV := generatorCoordinates35 3
    terms := 8
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 14
    coordinateU := generatorCoordinates48 0
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 15
    coordinateU := generatorCoordinates48 0
    coordinateV := generatorCoordinates35 3
    terms := 8
    radialRoot := generatorRadialRoots 3 53
  },
  {
    rectangle := generatorPartitionRectangles 50 16
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates33 7
    terms := 20
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 50 17
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates33 6
    terms := 8
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 50 18
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 50 19
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 50 20
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 50 21
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates32 5
    terms := 12
    radialRoot := generatorRadialRoots 3 60
  },
  {
    rectangle := generatorPartitionRectangles 50 22
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates32 4
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 50 23
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates32 5
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 50 24
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates32 4
    terms := 12
    radialRoot := generatorRadialRoots 3 58
  },
  {
    rectangle := generatorPartitionRectangles 50 25
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 50 26
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 50 27
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 50 28
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates30 3
    terms := 30
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 50 29
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates30 2
    terms := 20
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 30
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 31
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 50 32
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 50 33
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 34
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 50 35
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 50 36
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates29 4
    terms := 20
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 50 37
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates30 1
    terms := 20
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 50 38
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 50 39
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 50 40
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 50 41
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 50 42
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 50 43
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 50 44
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 50 45
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates29 3
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 50 46
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 50 47
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 50 48
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 50 49
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 50 50
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 50 51
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 50 52
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 50 53
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 50 54
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates29 4
    terms := 20
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 50 55
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 50 56
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 50 57
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 50 58
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 50 59
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 50 60
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 50 61
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 50 62
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 50 63
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates29 3
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks50_valid : ∀ i, (generatorLeafBlocks50 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks50 i).coordinateU.IsValid ∧
      (generatorLeafBlocks50 i).coordinateV.IsValid ∧
      (generatorLeafBlocks50 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates48_valid 1,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 55⟩
    · exact ⟨generatorCoordinates48_valid 1,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates48_valid 0,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates48_valid 0,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 53⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates32_valid 5, generatorRadialRoots_valid 3 60⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates32_valid 4, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates32_valid 5, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates32_valid 4, generatorRadialRoots_valid 3 58⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 42⟩
  have hMeta : ∀ i, (generatorLeafBlocks50 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks50 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
