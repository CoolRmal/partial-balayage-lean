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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates44

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 57 of the recorded finite partition. -/
def generatorLeafBlocks57 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 57 0
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 57 1
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 57 2
    coordinateU := generatorCoordinates44 0
    coordinateV := generatorCoordinates34 6
    terms := 8
    radialRoot := generatorRadialRoots 3 39
  },
  {
    rectangle := generatorPartitionRectangles 57 3
    coordinateU := generatorCoordinates44 0
    coordinateV := generatorCoordinates34 5
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 4
    coordinateU := generatorCoordinates43 7
    coordinateV := generatorCoordinates34 6
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 5
    coordinateU := generatorCoordinates43 7
    coordinateV := generatorCoordinates34 5
    terms := 5
    radialRoot := generatorRadialRoots 3 37
  },
  {
    rectangle := generatorPartitionRectangles 57 6
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates33 6
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 7
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 8
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates34 0
    terms := 5
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 57 9
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates33 7
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 10
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates34 0
    terms := 4
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 11
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates33 7
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 12
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates33 6
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 13
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 14
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates33 6
    terms := 5
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 15
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 16
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 57 17
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 57 18
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 57 19
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 57 20
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 57 21
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 22
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 23
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 24
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 57 25
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 26
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 57 27
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 28
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 29
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 30
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 31
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 32
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 33
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 34
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 35
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 36
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 37
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 38
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 39
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 57 40
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 41
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 42
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 43
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 57 44
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 57 45
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 57 46
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 57 47
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 57 48
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 57 49
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 50
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 57 51
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 52
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 53
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 54
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 55
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 57 56
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 57 57
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates30 4
    terms := 5
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 58
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 57 59
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates30 4
    terms := 5
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 57 60
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 57 61
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 57 62
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates30 3
    terms := 5
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 57 63
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks57_valid : ∀ i, (generatorLeafBlocks57 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks57 i).coordinateU.IsValid ∧
      (generatorLeafBlocks57 i).coordinateV.IsValid ∧
      (generatorLeafBlocks57 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates44_valid 0,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 39⟩
    · exact ⟨generatorCoordinates44_valid 0,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates43_valid 7,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates43_valid 7,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 37⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 30⟩
  have hMeta : ∀ i, (generatorLeafBlocks57 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks57 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
