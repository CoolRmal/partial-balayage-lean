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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates88

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 105 of the recorded finite partition. -/
def generatorLeafBlocks105 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 105 0
    coordinateU := generatorCoordinates6 0
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 4
  },
  {
    rectangle := generatorPartitionRectangles 105 1
    coordinateU := generatorCoordinates5 2
    coordinateV := generatorCoordinates0 4
    terms := 0
    radialRoot := generatorRadialRoots 0 5
  },
  {
    rectangle := generatorPartitionRectangles 105 2
    coordinateU := generatorCoordinates5 7
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 4
  },
  {
    rectangle := generatorPartitionRectangles 105 3
    coordinateU := generatorCoordinates5 7
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 3
  },
  {
    rectangle := generatorPartitionRectangles 105 4
    coordinateU := generatorCoordinates5 6
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 3
  },
  {
    rectangle := generatorPartitionRectangles 105 5
    coordinateU := generatorCoordinates5 6
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 2
  },
  {
    rectangle := generatorPartitionRectangles 105 6
    coordinateU := generatorCoordinates0 6
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 9
  },
  {
    rectangle := generatorPartitionRectangles 105 7
    coordinateU := generatorCoordinates0 6
    coordinateV := generatorCoordinates0 5
    terms := 0
    radialRoot := generatorRadialRoots 0 5
  },
  {
    rectangle := generatorPartitionRectangles 105 8
    coordinateU := generatorCoordinates0 5
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 5
  },
  {
    rectangle := generatorPartitionRectangles 105 9
    coordinateU := generatorCoordinates0 5
    coordinateV := generatorCoordinates0 5
    terms := 0
    radialRoot := generatorRadialRoots 0 3
  },
  {
    rectangle := generatorPartitionRectangles 105 10
    coordinateU := generatorCoordinates0 6
    coordinateV := generatorCoordinates0 4
    terms := 0
    radialRoot := generatorRadialRoots 0 3
  },
  {
    rectangle := generatorPartitionRectangles 105 11
    coordinateU := generatorCoordinates0 6
    coordinateV := generatorCoordinates0 3
    terms := 0
    radialRoot := generatorRadialRoots 0 1
  },
  {
    rectangle := generatorPartitionRectangles 105 12
    coordinateU := generatorCoordinates0 5
    coordinateV := generatorCoordinates0 4
    terms := 0
    radialRoot := generatorRadialRoots 0 1
  },
  {
    rectangle := generatorPartitionRectangles 105 13
    coordinateU := generatorCoordinates0 5
    coordinateV := generatorCoordinates0 3
    terms := 0
    radialRoot := generatorRadialRoots 0 0
  },
  {
    rectangle := generatorPartitionRectangles 105 14
    coordinateU := generatorCoordinates0 4
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 3
  },
  {
    rectangle := generatorPartitionRectangles 105 15
    coordinateU := generatorCoordinates0 4
    coordinateV := generatorCoordinates0 5
    terms := 0
    radialRoot := generatorRadialRoots 0 1
  },
  {
    rectangle := generatorPartitionRectangles 105 16
    coordinateU := generatorCoordinates0 3
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 1
  },
  {
    rectangle := generatorPartitionRectangles 105 17
    coordinateU := generatorCoordinates0 3
    coordinateV := generatorCoordinates0 5
    terms := 0
    radialRoot := generatorRadialRoots 0 0
  },
  {
    rectangle := generatorPartitionRectangles 105 18
    coordinateU := generatorCoordinates0 1
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 0 1
  },
  {
    rectangle := generatorPartitionRectangles 105 19
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 20
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 21
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 22
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 23
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 24
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 25
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 26
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 27
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 28
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 29
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 30
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 31
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 32
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 33
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 34
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 35
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 36
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 37
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 38
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 39
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 40
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 41
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 42
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 43
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 44
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 45
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 46
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 47
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 48
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 49
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 50
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 51
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 52
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 53
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 54
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 55
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 56
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 57
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 58
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 59
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 60
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 61
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 62
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 105 63
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks105_valid : ∀ i, (generatorLeafBlocks105 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks105 i).coordinateU.IsValid ∧
      (generatorLeafBlocks105 i).coordinateV.IsValid ∧
      (generatorLeafBlocks105 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates6_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 4⟩
    · exact ⟨generatorCoordinates5_valid 2,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 0 5⟩
    · exact ⟨generatorCoordinates5_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 4⟩
    · exact ⟨generatorCoordinates5_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 3⟩
    · exact ⟨generatorCoordinates5_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 3⟩
    · exact ⟨generatorCoordinates5_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 2⟩
    · exact ⟨generatorCoordinates0_valid 6,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 9⟩
    · exact ⟨generatorCoordinates0_valid 6,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 0 5⟩
    · exact ⟨generatorCoordinates0_valid 5,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 5⟩
    · exact ⟨generatorCoordinates0_valid 5,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 0 3⟩
    · exact ⟨generatorCoordinates0_valid 6,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 0 3⟩
    · exact ⟨generatorCoordinates0_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 0 1⟩
    · exact ⟨generatorCoordinates0_valid 5,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 0 1⟩
    · exact ⟨generatorCoordinates0_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 0 0⟩
    · exact ⟨generatorCoordinates0_valid 4,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 3⟩
    · exact ⟨generatorCoordinates0_valid 4,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 0 1⟩
    · exact ⟨generatorCoordinates0_valid 3,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 1⟩
    · exact ⟨generatorCoordinates0_valid 3,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 0 0⟩
    · exact ⟨generatorCoordinates0_valid 1,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 0 1⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
  have hMeta : ∀ i, (generatorLeafBlocks105 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks105 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
