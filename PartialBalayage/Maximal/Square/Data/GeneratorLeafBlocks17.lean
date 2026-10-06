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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates64
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates66
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates68

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 17 of the recorded finite partition. -/
def generatorLeafBlocks17 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 17 0
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 17 1
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 17 2
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 17 3
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 17 4
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 17 5
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 17 6
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 17 7
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 17 8
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 17 9
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 17 10
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 17 11
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 17 12
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 17 13
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 17 14
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 17 15
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 17 16
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 17 17
    coordinateU := generatorCoordinates64 7
    coordinateV := generatorCoordinates46 2
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 17 18
    coordinateU := generatorCoordinates64 6
    coordinateV := generatorCoordinates46 3
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 17 19
    coordinateU := generatorCoordinates64 6
    coordinateV := generatorCoordinates46 2
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 17 20
    coordinateU := generatorCoordinates64 5
    coordinateV := generatorCoordinates41 2
    terms := 12
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 17 21
    coordinateU := generatorCoordinates64 7
    coordinateV := generatorCoordinates36 7
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 17 22
    coordinateU := generatorCoordinates64 7
    coordinateV := generatorCoordinates36 6
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 17 23
    coordinateU := generatorCoordinates64 6
    coordinateV := generatorCoordinates36 7
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 17 24
    coordinateU := generatorCoordinates64 6
    coordinateV := generatorCoordinates36 6
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 17 25
    coordinateU := generatorCoordinates64 7
    coordinateV := generatorCoordinates33 0
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 17 26
    coordinateU := generatorCoordinates64 7
    coordinateV := generatorCoordinates32 7
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 17 27
    coordinateU := generatorCoordinates64 6
    coordinateV := generatorCoordinates33 0
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 17 28
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates33 2
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 17 29
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates33 1
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 17 30
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates33 2
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 17 31
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates33 1
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 17 32
    coordinateU := generatorCoordinates64 7
    coordinateV := generatorCoordinates29 1
    terms := 4
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 17 33
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates29 3
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 17 34
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates29 2
    terms := 5
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 17 35
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates29 3
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 17 36
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 17 37
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates29 5
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 17 38
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates29 4
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 17 39
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates29 5
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 17 40
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates29 4
    terms := 30
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 17 41
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates29 3
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 17 42
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates29 7
    terms := 3
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 17 43
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 17 44
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates29 7
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 17 45
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 17 46
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates30 1
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 17 47
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates30 0
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 17 48
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 17 49
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 17 50
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 17 51
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 17 52
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 17 53
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 17 54
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates26 6
    terms := 3
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 17 55
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates26 5
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 17 56
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates26 6
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 17 57
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 17 58
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 17 59
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 17 60
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 17 61
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates26 3
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 17 62
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 17 63
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks17_valid : ∀ i, (generatorLeafBlocks17 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks17 i).coordinateU.IsValid ∧
      (generatorLeafBlocks17 i).coordinateV.IsValid ∧
      (generatorLeafBlocks17 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates64_valid 7,
        generatorCoordinates46_valid 2, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates64_valid 6,
        generatorCoordinates46_valid 3, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates64_valid 6,
        generatorCoordinates46_valid 2, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates64_valid 5,
        generatorCoordinates41_valid 2, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates64_valid 7,
        generatorCoordinates36_valid 7, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates64_valid 7,
        generatorCoordinates36_valid 6, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates64_valid 6,
        generatorCoordinates36_valid 7, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates64_valid 6,
        generatorCoordinates36_valid 6, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates64_valid 7,
        generatorCoordinates33_valid 0, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates64_valid 7,
        generatorCoordinates32_valid 7, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates64_valid 6,
        generatorCoordinates33_valid 0, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates64_valid 7,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 5 2⟩
  have hMeta : ∀ i, (generatorLeafBlocks17 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks17 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
