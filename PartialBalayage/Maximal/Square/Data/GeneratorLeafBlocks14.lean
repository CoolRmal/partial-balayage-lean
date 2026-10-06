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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates24
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates66
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates68
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates70

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 14 of the recorded finite partition. -/
def generatorLeafBlocks14 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 14 0
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 14 1
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 14 2
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 14 3
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 14 4
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 14 5
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 14 6
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 14 7
    coordinateU := generatorCoordinates67 4
    coordinateV := generatorCoordinates41 3
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 14 8
    coordinateU := generatorCoordinates67 3
    coordinateV := generatorCoordinates41 4
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 14 9
    coordinateU := generatorCoordinates67 3
    coordinateV := generatorCoordinates41 3
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 14 10
    coordinateU := generatorCoordinates67 2
    coordinateV := generatorCoordinates36 5
    terms := 20
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 14 11
    coordinateU := generatorCoordinates67 4
    coordinateV := generatorCoordinates33 0
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 14 12
    coordinateU := generatorCoordinates67 4
    coordinateV := generatorCoordinates32 7
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 14 13
    coordinateU := generatorCoordinates67 3
    coordinateV := generatorCoordinates33 0
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 14 14
    coordinateU := generatorCoordinates67 3
    coordinateV := generatorCoordinates32 7
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 14 15
    coordinateU := generatorCoordinates67 4
    coordinateV := generatorCoordinates29 1
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 14 16
    coordinateU := generatorCoordinates67 4
    coordinateV := generatorCoordinates29 0
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 14 17
    coordinateU := generatorCoordinates67 3
    coordinateV := generatorCoordinates29 1
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 14 18
    coordinateU := generatorCoordinates67 3
    coordinateV := generatorCoordinates29 0
    terms := 30
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 14 19
    coordinateU := generatorCoordinates67 4
    coordinateV := generatorCoordinates25 2
    terms := 4
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 14 20
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates25 4
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 14 21
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates25 3
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 14 22
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates25 4
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 14 23
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates26 0
    terms := 2
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 14 24
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates25 7
    terms := 4
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 14 25
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates26 0
    terms := 3
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 14 26
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates25 7
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 14 27
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates25 6
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 14 28
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates25 5
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 14 29
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates25 6
    terms := 5
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 14 30
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates25 5
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 14 31
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates25 4
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 14 32
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 14 33
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 34
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 35
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 14 36
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates26 2
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 14 37
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates26 1
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 38
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 39
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 14 40
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 14 41
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 14 42
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 14 43
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 14 44
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates23 1
    terms := 3
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 14 45
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates23 0
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 14 46
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 14 47
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 14 48
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates22 7
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 14 49
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates22 6
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 50
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates22 7
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 51
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates22 6
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 14 52
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 14 53
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates23 0
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 54
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 14 55
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates23 0
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 14 56
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates22 7
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 14 57
    coordinateU := generatorCoordinates69 6
    coordinateV := generatorCoordinates24 1
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 14 58
    coordinateU := generatorCoordinates69 6
    coordinateV := generatorCoordinates24 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 14 59
    coordinateU := generatorCoordinates69 5
    coordinateV := generatorCoordinates24 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 14 60
    coordinateU := generatorCoordinates69 5
    coordinateV := generatorCoordinates24 0
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 14 61
    coordinateU := generatorCoordinates69 4
    coordinateV := generatorCoordinates24 3
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 14 62
    coordinateU := generatorCoordinates69 4
    coordinateV := generatorCoordinates24 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 14 63
    coordinateU := generatorCoordinates69 3
    coordinateV := generatorCoordinates24 3
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks14_valid : ∀ i, (generatorLeafBlocks14 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks14 i).coordinateU.IsValid ∧
      (generatorLeafBlocks14 i).coordinateV.IsValid ∧
      (generatorLeafBlocks14 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates67_valid 4,
        generatorCoordinates41_valid 3, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates67_valid 3,
        generatorCoordinates41_valid 4, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates67_valid 3,
        generatorCoordinates41_valid 3, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates67_valid 2,
        generatorCoordinates36_valid 5, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates67_valid 4,
        generatorCoordinates33_valid 0, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates67_valid 4,
        generatorCoordinates32_valid 7, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates67_valid 3,
        generatorCoordinates33_valid 0, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates67_valid 3,
        generatorCoordinates32_valid 7, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates67_valid 4,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates67_valid 4,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates67_valid 3,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates67_valid 3,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates67_valid 4,
        generatorCoordinates25_valid 2, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates69_valid 6,
        generatorCoordinates24_valid 1, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates69_valid 6,
        generatorCoordinates24_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates69_valid 5,
        generatorCoordinates24_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates69_valid 5,
        generatorCoordinates24_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates69_valid 4,
        generatorCoordinates24_valid 3, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates69_valid 4,
        generatorCoordinates24_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates69_valid 3,
        generatorCoordinates24_valid 3, generatorRadialRoots_valid 4 62⟩
  have hMeta : ∀ i, (generatorLeafBlocks14 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks14 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
