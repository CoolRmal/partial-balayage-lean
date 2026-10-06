/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates27

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 81 of the recorded finite partition. -/
def generatorLeafBlocks81 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 81 0
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates25 7
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 81 1
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 81 2
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates25 7
    terms := 5
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 81 3
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates25 4
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 81 4
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 81 5
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 81 6
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 81 7
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 81 8
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates25 6
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 81 9
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates25 5
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 81 10
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates26 6
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 81 11
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates26 5
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 81 12
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates26 6
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 81 13
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates26 5
    terms := 5
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 81 14
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates26 4
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 81 15
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates26 3
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 81 16
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 81 17
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 81 18
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 81 19
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 81 20
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates27 0
    terms := 4
    radialRoot := generatorRadialRoots 2 36
  },
  {
    rectangle := generatorPartitionRectangles 81 21
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates26 7
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 22
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates27 0
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 23
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates26 7
    terms := 4
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 81 24
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates26 0
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 25
    coordinateU := generatorCoordinates27 4
    coordinateV := generatorCoordinates27 0
    terms := 4
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 81 26
    coordinateU := generatorCoordinates27 4
    coordinateV := generatorCoordinates26 7
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 81 27
    coordinateU := generatorCoordinates27 3
    coordinateV := generatorCoordinates27 0
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 81 28
    coordinateU := generatorCoordinates27 3
    coordinateV := generatorCoordinates26 7
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 81 29
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates26 2
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 81 30
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates26 1
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 31
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates27 6
    terms := 4
    radialRoot := generatorRadialRoots 2 36
  },
  {
    rectangle := generatorPartitionRectangles 81 32
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates27 5
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 33
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates27 6
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 34
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates27 5
    terms := 4
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 81 35
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates27 4
    terms := 4
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 81 36
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates27 3
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 81 37
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates27 4
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 81 38
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates27 3
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 81 39
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates26 0
    terms := 5
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 81 40
    coordinateU := generatorCoordinates27 2
    coordinateV := generatorCoordinates27 0
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 81 41
    coordinateU := generatorCoordinates27 2
    coordinateV := generatorCoordinates26 7
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 81 42
    coordinateU := generatorCoordinates27 1
    coordinateV := generatorCoordinates27 0
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 81 43
    coordinateU := generatorCoordinates27 1
    coordinateV := generatorCoordinates26 7
    terms := 3
    radialRoot := generatorRadialRoots 2 30
  },
  {
    rectangle := generatorPartitionRectangles 81 44
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates27 2
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 81 45
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates27 1
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 81 46
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates27 2
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 81 47
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates27 1
    terms := 3
    radialRoot := generatorRadialRoots 2 30
  },
  {
    rectangle := generatorPartitionRectangles 81 48
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates27 0
    terms := 3
    radialRoot := generatorRadialRoots 2 30
  },
  {
    rectangle := generatorPartitionRectangles 81 49
    coordinateU := generatorCoordinates27 0
    coordinateV := generatorCoordinates26 7
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 81 50
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates27 0
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 81 51
    coordinateU := generatorCoordinates26 7
    coordinateV := generatorCoordinates26 7
    terms := 3
    radialRoot := generatorRadialRoots 2 28
  },
  {
    rectangle := generatorPartitionRectangles 81 52
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 81 53
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates23 0
    terms := 3
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 81 54
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 81 55
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates23 0
    terms := 3
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 81 56
    coordinateU := generatorCoordinates25 6
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 57
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 81 58
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates23 0
    terms := 3
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 59
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 81 60
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates23 0
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 81 61
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates22 0
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 81 62
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates22 5
    terms := 2
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 81 63
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates22 4
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks81_valid : ∀ i, (generatorLeafBlocks81 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks81 i).coordinateU.IsValid ∧
      (generatorLeafBlocks81 i).coordinateV.IsValid ∧
      (generatorLeafBlocks81 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 36⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates27_valid 4,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates27_valid 4,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates27_valid 3,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates27_valid 3,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates27_valid 6, generatorRadialRoots_valid 2 36⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates27_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates27_valid 6, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates27_valid 5, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates27_valid 4, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates27_valid 3, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates27_valid 4, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates27_valid 3, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates27_valid 2,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates27_valid 2,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates27_valid 1,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates27_valid 1,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 30⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates27_valid 2, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates27_valid 1, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates27_valid 2, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates27_valid 1, generatorRadialRoots_valid 2 30⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 30⟩
    · exact ⟨generatorCoordinates27_valid 0,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates27_valid 0, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates26_valid 7,
        generatorCoordinates26_valid 7, generatorRadialRoots_valid 2 28⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates25_valid 6,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 2 31⟩
  have hMeta : ∀ i, (generatorLeafBlocks81 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks81 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
