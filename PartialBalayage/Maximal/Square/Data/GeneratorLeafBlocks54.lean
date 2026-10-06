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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 54 of the recorded finite partition. -/
def generatorLeafBlocks54 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 54 0
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 54 1
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 54 2
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 54 3
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 54 4
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 54 5
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 54 6
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 54 7
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 54 8
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 54 9
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 54 10
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates5 5
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 54 11
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates5 4
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 54 12
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates6 5
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 54 13
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates6 4
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 54 14
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates6 5
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 54 15
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates6 4
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 54 16
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 54 17
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 54 18
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 54 19
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates5 6
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 54 20
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 54 21
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 54 22
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 54 23
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 54 24
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 25
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 26
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 54 27
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates1 6
    terms := 5
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 54 28
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 54 29
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates1 6
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 54 30
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 54 31
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 54 32
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 54 33
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 54 34
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 54 35
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates1 6
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 54 36
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 54 37
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates1 6
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 54 38
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 54 39
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 54 40
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 41
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 42
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 54 43
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates1 2
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 54 44
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 45
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates1 2
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 46
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 54 47
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 54 48
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates1 2
    terms := 4
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 54 49
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 54 50
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates1 2
    terms := 4
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 54 51
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 54 52
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 54 53
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates1 6
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 54 54
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 55
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates1 6
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 54 56
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 54 57
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 54 58
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 54 59
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 54 60
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 54 61
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates1 6
    terms := 4
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 54 62
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 54 63
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks54_valid : ∀ i, (generatorLeafBlocks54 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks54 i).coordinateU.IsValid ∧
      (generatorLeafBlocks54 i).coordinateV.IsValid ∧
      (generatorLeafBlocks54 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 27⟩
  have hMeta : ∀ i, (generatorLeafBlocks54 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks54 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
