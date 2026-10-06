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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
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

/-- Actual source leaf candidates, block 51 of the recorded finite partition. -/
def generatorLeafBlocks51 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 51 0
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 51 1
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 2
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 3
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 51 4
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 51 5
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 6
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 7
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 51 8
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 51 9
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 51 10
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 51 11
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 51 12
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 51 13
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 51 14
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 51 15
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 51 16
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 51 17
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 18
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 19
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 51 20
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 51 21
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 22
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 51 23
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 51 24
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 51 25
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 51 26
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 51 27
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 51 28
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 51 29
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 51 30
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 51 31
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 51 32
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 51 33
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 51 34
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 51 35
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 51 36
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 51 37
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 51 38
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 51 39
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 51 40
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 51 41
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 51 42
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 51 43
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 51 44
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 51 45
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 51 46
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 51 47
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 51 48
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 51 49
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 51 50
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 51 51
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 51 52
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 51 53
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 51 54
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 51 55
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 51 56
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 51 57
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 51 58
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 51 59
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 51 60
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 51 61
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 51 62
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 51 63
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks51_valid : ∀ i, (generatorLeafBlocks51 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks51 i).coordinateU.IsValid ∧
      (generatorLeafBlocks51 i).coordinateV.IsValid ∧
      (generatorLeafBlocks51 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 29⟩
  have hMeta : ∀ i, (generatorLeafBlocks51 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks51 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
