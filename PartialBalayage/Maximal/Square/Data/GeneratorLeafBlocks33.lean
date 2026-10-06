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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates56

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 33 of the recorded finite partition. -/
def generatorLeafBlocks33 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 33 0
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates37 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 33 1
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates37 7
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 33 2
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates37 6
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 33 3
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates37 0
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 33 4
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates37 7
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 33 5
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates37 6
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 33 6
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates37 7
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 33 7
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates37 6
    terms := 8
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 33 8
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates37 5
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 33 9
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates37 4
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 33 10
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates37 5
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 33 11
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates37 4
    terms := 12
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 33 12
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates33 4
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 33 13
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates33 3
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 33 14
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates33 4
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 33 15
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates33 3
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 33 16
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates33 2
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 33 17
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates33 1
    terms := 30
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 33 18
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates33 2
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 33 19
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates33 1
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 33 20
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates33 4
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 33 21
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates33 3
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 33 22
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 33 23
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 33 24
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates34 4
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 33 25
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates34 3
    terms := 20
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 33 26
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 33 27
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates34 1
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 33 28
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates34 2
    terms := 30
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 33 29
    coordinateU := generatorCoordinates57 1
    coordinateV := generatorCoordinates35 6
    terms := 12
    radialRoot := generatorRadialRoots 4 29
  },
  {
    rectangle := generatorPartitionRectangles 33 30
    coordinateU := generatorCoordinates57 1
    coordinateV := generatorCoordinates35 5
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 33 31
    coordinateU := generatorCoordinates57 0
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 33 32
    coordinateU := generatorCoordinates57 0
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 27
  },
  {
    rectangle := generatorPartitionRectangles 33 33
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates33 2
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 33 34
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 33 35
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 36
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 37
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 33 38
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 33 39
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 40
    coordinateU := generatorCoordinates57 1
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 27
  },
  {
    rectangle := generatorPartitionRectangles 33 41
    coordinateU := generatorCoordinates57 1
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 42
    coordinateU := generatorCoordinates57 0
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 43
    coordinateU := generatorCoordinates57 0
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 25
  },
  {
    rectangle := generatorPartitionRectangles 33 44
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates33 7
    terms := 30
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 33 45
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 33 46
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 33 47
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates33 6
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 33 48
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates33 5
    terms := 20
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 33 49
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 33 50
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 33 51
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 33 52
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 33 53
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates30 3
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 33 54
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates30 2
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 55
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates30 3
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 56
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates30 2
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 33 57
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates30 5
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 33 58
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 59
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates30 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 33 60
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 33 61
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates29 4
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 33 62
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates29 3
    terms := 30
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 33 63
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks33_valid : ∀ i, (generatorLeafBlocks33 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks33 i).coordinateU.IsValid ∧
      (generatorLeafBlocks33 i).coordinateV.IsValid ∧
      (generatorLeafBlocks33 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates33_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates33_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates33_valid 4, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates57_valid 1,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 29⟩
    · exact ⟨generatorCoordinates57_valid 1,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates57_valid 0,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates57_valid 0,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 27⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates57_valid 1,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 27⟩
    · exact ⟨generatorCoordinates57_valid 1,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates57_valid 0,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates57_valid 0,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 25⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 17⟩
  have hMeta : ∀ i, (generatorLeafBlocks33 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks33 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
