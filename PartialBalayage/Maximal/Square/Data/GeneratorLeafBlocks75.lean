/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 75 of the recorded finite partition. -/
def generatorLeafBlocks75 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 75 0
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 75 1
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 75 2
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 75 3
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 75 4
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 75 5
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 75 6
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 75 7
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 75 8
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 75 9
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 75 10
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates25 6
    terms := 3
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 75 11
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates25 5
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 75 12
    coordinateU := generatorCoordinates29 2
    coordinateV := generatorCoordinates25 6
    terms := 3
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 75 13
    coordinateU := generatorCoordinates29 2
    coordinateV := generatorCoordinates25 5
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 75 14
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates25 4
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 75 15
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 75 16
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 75 17
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 75 18
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates25 7
    terms := 5
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 75 19
    coordinateU := generatorCoordinates29 2
    coordinateV := generatorCoordinates25 4
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 75 20
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 75 21
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates25 7
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 75 22
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 75 23
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates25 7
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 75 24
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 75 25
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 75 26
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 75 27
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 75 28
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates22 0
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 75 29
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 75 30
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 75 31
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 75 32
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 75 33
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates22 0
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 75 34
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates21 7
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 75 35
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 75 36
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 75 37
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 75 38
    coordinateU := generatorCoordinates32 3
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 42
  },
  {
    rectangle := generatorPartitionRectangles 75 39
    coordinateU := generatorCoordinates32 3
    coordinateV := generatorCoordinates23 2
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 75 40
    coordinateU := generatorCoordinates32 2
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 75 41
    coordinateU := generatorCoordinates32 2
    coordinateV := generatorCoordinates23 2
    terms := 4
    radialRoot := generatorRadialRoots 2 40
  },
  {
    rectangle := generatorPartitionRectangles 75 42
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates21 7
    terms := 3
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 75 43
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 75 44
    coordinateU := generatorCoordinates32 1
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 40
  },
  {
    rectangle := generatorPartitionRectangles 75 45
    coordinateU := generatorCoordinates32 1
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 75 46
    coordinateU := generatorCoordinates32 0
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 75 47
    coordinateU := generatorCoordinates32 0
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 38
  },
  {
    rectangle := generatorPartitionRectangles 75 48
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 75 49
    coordinateU := generatorCoordinates31 7
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 38
  },
  {
    rectangle := generatorPartitionRectangles 75 50
    coordinateU := generatorCoordinates31 7
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 75 51
    coordinateU := generatorCoordinates31 6
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 75 52
    coordinateU := generatorCoordinates31 6
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 36
  },
  {
    rectangle := generatorPartitionRectangles 75 53
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 75 54
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 75 55
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 75 56
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 75 57
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates22 0
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 75 58
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 75 59
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 75 60
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 75 61
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates23 0
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 75 62
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates22 7
    terms := 3
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 75 63
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates22 6
    terms := 3
    radialRoot := generatorRadialRoots 2 39
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks75_valid : ∀ i, (generatorLeafBlocks75 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks75 i).coordinateU.IsValid ∧
      (generatorLeafBlocks75 i).coordinateV.IsValid ∧
      (generatorLeafBlocks75 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates29_valid 2,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates29_valid 2,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates29_valid 2,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates32_valid 3,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 42⟩
    · exact ⟨generatorCoordinates32_valid 3,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates32_valid 2,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates32_valid 2,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 40⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates32_valid 1,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 40⟩
    · exact ⟨generatorCoordinates32_valid 1,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates32_valid 0,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates32_valid 0,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 38⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates31_valid 7,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 38⟩
    · exact ⟨generatorCoordinates31_valid 7,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates31_valid 6,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates31_valid 6,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 36⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 2 39⟩
  have hMeta : ∀ i, (generatorLeafBlocks75 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks75 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
