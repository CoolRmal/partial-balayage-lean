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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
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

/-- Actual source leaf candidates, block 46 of the recorded finite partition. -/
def generatorLeafBlocks46 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 46 0
    coordinateU := generatorCoordinates46 2
    coordinateV := generatorCoordinates46 2
    terms := 0
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 46 1
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 46 2
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates41 7
    terms := 5
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 46 3
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 46 4
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates41 7
    terms := 0
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 46 5
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates42 4
    terms := 0
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 46 6
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates42 3
    terms := 1
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 46 7
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates42 4
    terms := 0
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 46 8
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates42 3
    terms := 0
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 46 9
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates42 2
    terms := 2
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 46 10
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates43 2
    terms := 1
    radialRoot := generatorRadialRoots 4 35
  },
  {
    rectangle := generatorPartitionRectangles 46 11
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates43 1
    terms := 2
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 46 12
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates43 2
    terms := 0
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 46 13
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates43 1
    terms := 1
    radialRoot := generatorRadialRoots 4 33
  },
  {
    rectangle := generatorPartitionRectangles 46 14
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates42 2
    terms := 0
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 46 15
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates42 1
    terms := 1
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 46 16
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates41 6
    terms := 0
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 46 17
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates42 2
    terms := 0
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 46 18
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates42 1
    terms := 0
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 46 19
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates42 2
    terms := 0
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 46 20
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates42 1
    terms := 0
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 46 21
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 46 22
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates41 7
    terms := 0
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 46 23
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 46 24
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates41 7
    terms := 0
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 46 25
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates41 6
    terms := 0
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 46 26
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates41 5
    terms := 0
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 46 27
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates41 6
    terms := 0
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 46 28
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates41 5
    terms := 0
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 46 29
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates40 3
    terms := 3
    radialRoot := generatorRadialRoots 4 33
  },
  {
    rectangle := generatorPartitionRectangles 46 30
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates40 2
    terms := 3
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 46 31
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates40 3
    terms := 1
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 46 32
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates40 2
    terms := 2
    radialRoot := generatorRadialRoots 4 31
  },
  {
    rectangle := generatorPartitionRectangles 46 33
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates40 1
    terms := 4
    radialRoot := generatorRadialRoots 4 31
  },
  {
    rectangle := generatorPartitionRectangles 46 34
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates40 0
    terms := 5
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 46 35
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates40 1
    terms := 2
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 46 36
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates40 0
    terms := 3
    radialRoot := generatorRadialRoots 4 29
  },
  {
    rectangle := generatorPartitionRectangles 46 37
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates38 3
    terms := 3
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 46 38
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates38 2
    terms := 3
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 46 39
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 7
    terms := 5
    radialRoot := generatorRadialRoots 4 29
  },
  {
    rectangle := generatorPartitionRectangles 46 40
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 6
    terms := 8
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 46 41
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 7
    terms := 4
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 46 42
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 6
    terms := 5
    radialRoot := generatorRadialRoots 4 27
  },
  {
    rectangle := generatorPartitionRectangles 46 43
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 5
    terms := 8
    radialRoot := generatorRadialRoots 4 27
  },
  {
    rectangle := generatorPartitionRectangles 46 44
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 4
    terms := 8
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 46 45
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 5
    terms := 8
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 46 46
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 4
    terms := 8
    radialRoot := generatorRadialRoots 4 25
  },
  {
    rectangle := generatorPartitionRectangles 46 47
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates38 1
    terms := 8
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 46 48
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates38 0
    terms := 12
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 46 49
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates38 3
    terms := 1
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 46 50
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates38 2
    terms := 1
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 46 51
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates38 3
    terms := 0
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 46 52
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates38 2
    terms := 1
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 46 53
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates38 1
    terms := 4
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 46 54
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates38 0
    terms := 8
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 46 55
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates38 1
    terms := 2
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 46 56
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates38 0
    terms := 5
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 46 57
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 3
    terms := 8
    radialRoot := generatorRadialRoots 4 25
  },
  {
    rectangle := generatorPartitionRectangles 46 58
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 2
    terms := 12
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 46 59
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 3
    terms := 8
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 46 60
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 2
    terms := 8
    radialRoot := generatorRadialRoots 4 23
  },
  {
    rectangle := generatorPartitionRectangles 46 61
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 1
    terms := 12
    radialRoot := generatorRadialRoots 4 23
  },
  {
    rectangle := generatorPartitionRectangles 46 62
    coordinateU := generatorCoordinates49 3
    coordinateV := generatorCoordinates39 0
    terms := 12
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 46 63
    coordinateU := generatorCoordinates49 2
    coordinateV := generatorCoordinates39 1
    terms := 12
    radialRoot := generatorRadialRoots 4 22
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks46_valid : ∀ i, (generatorLeafBlocks46 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks46 i).coordinateU.IsValid ∧
      (generatorLeafBlocks46 i).coordinateV.IsValid ∧
      (generatorLeafBlocks46 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates46_valid 2,
        generatorCoordinates46_valid 2, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates42_valid 4, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates42_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates42_valid 4, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates42_valid 3, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 35⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 33⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates40_valid 3, generatorRadialRoots_valid 4 33⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates40_valid 2, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates40_valid 3, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates40_valid 2, generatorRadialRoots_valid 4 31⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates40_valid 1, generatorRadialRoots_valid 4 31⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates40_valid 0, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates40_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates40_valid 0, generatorRadialRoots_valid 4 29⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 4 29⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 7, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 6, generatorRadialRoots_valid 4 27⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 5, generatorRadialRoots_valid 4 27⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 4, generatorRadialRoots_valid 4 25⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 25⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 3, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 2, generatorRadialRoots_valid 4 23⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 23⟩
    · exact ⟨generatorCoordinates49_valid 3,
        generatorCoordinates39_valid 0, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates49_valid 2,
        generatorCoordinates39_valid 1, generatorRadialRoots_valid 4 22⟩
  have hMeta : ∀ i, (generatorLeafBlocks46 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks46 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
