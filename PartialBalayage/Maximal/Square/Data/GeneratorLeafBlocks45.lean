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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 45 of the recorded finite partition. -/
def generatorLeafBlocks45 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 45 0
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 45 1
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 45 2
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 45 3
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 45 4
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 45 5
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 45 6
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 45 7
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 45 8
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 45 9
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 10
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 11
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 45 12
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 45 13
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 45 14
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 45 15
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 45 16
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 45 17
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 45 18
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 45 19
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 45 20
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 45 21
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 45 22
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 45 23
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 45 24
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 45 25
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 26
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 27
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 45 28
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates1 2
    terms := 5
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 45 29
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 30
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates1 2
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 31
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 45 32
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 45 33
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 45 34
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 45 35
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 45 36
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 37
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 45 38
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 45 39
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 45 40
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 45 41
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 45 42
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 45 43
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 45 44
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 45 45
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 45 46
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 45 47
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 45 48
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 45 49
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 45 50
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 45 51
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 45 52
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 45 53
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 45 54
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 45 55
    coordinateU := generatorCoordinates46 3
    coordinateV := generatorCoordinates46 3
    terms := 0
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 45 56
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates46 5
    terms := 0
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 45 57
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates46 4
    terms := 0
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 45 58
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates46 5
    terms := 0
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 45 59
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates46 4
    terms := 0
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 45 60
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates46 7
    terms := 0
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 45 61
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates46 6
    terms := 0
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 45 62
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates46 7
    terms := 0
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 45 63
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates46 6
    terms := 0
    radialRoot := generatorRadialRoots 4 48
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks45_valid : ∀ i, (generatorLeafBlocks45 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks45 i).coordinateU.IsValid ∧
      (generatorLeafBlocks45 i).coordinateV.IsValid ∧
      (generatorLeafBlocks45 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates46_valid 3,
        generatorCoordinates46_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates46_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates46_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates46_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates46_valid 6, generatorRadialRoots_valid 4 48⟩
  have hMeta : ∀ i, (generatorLeafBlocks45 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks45 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
