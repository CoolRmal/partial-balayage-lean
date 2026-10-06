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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 63 of the recorded finite partition. -/
def generatorLeafBlocks63 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 63 0
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 63 1
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates33 5
    terms := 5
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 63 2
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 63 3
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates33 5
    terms := 4
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 63 4
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates33 2
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 63 5
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 63 6
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates33 5
    terms := 4
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 63 7
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 63 8
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates33 5
    terms := 4
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 63 9
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates34 4
    terms := 1
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 63 10
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 63 11
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates34 4
    terms := 1
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 63 12
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 63 13
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates33 3
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 63 14
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates34 4
    terms := 2
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 63 15
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates34 3
    terms := 2
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 63 16
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates34 4
    terms := 4
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 63 17
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates34 3
    terms := 3
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 63 18
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates34 2
    terms := 3
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 63 19
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates34 1
    terms := 3
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 63 20
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates34 2
    terms := 4
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 63 21
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates34 1
    terms := 4
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 63 22
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates33 2
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 63 23
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 63 24
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates33 5
    terms := 5
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 25
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 26
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates33 5
    terms := 5
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 63 27
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates34 0
    terms := 4
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 63 28
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates33 7
    terms := 4
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 29
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates34 0
    terms := 5
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 30
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates33 7
    terms := 5
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 63 31
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 63 32
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates33 5
    terms := 5
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 63 33
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates33 6
    terms := 5
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 63 34
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 63 35
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 63 36
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates30 4
    terms := 4
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 63 37
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates30 5
    terms := 4
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 63 38
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates30 4
    terms := 4
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 63 39
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates30 3
    terms := 5
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 63 40
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates30 2
    terms := 5
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 41
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates30 3
    terms := 5
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 42
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates30 2
    terms := 5
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 63 43
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 63 44
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates30 4
    terms := 4
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 45
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 63 46
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates30 4
    terms := 5
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 63 47
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates29 4
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 63 48
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates29 3
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 63 49
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates29 7
    terms := 5
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 63 50
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates29 6
    terms := 5
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 63 51
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates29 7
    terms := 5
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 63 52
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates29 6
    terms := 5
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 63 53
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates29 3
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 63 54
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates29 2
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 63 55
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 63 56
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates30 4
    terms := 5
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 63 57
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 63 58
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates30 4
    terms := 5
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 63 59
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates29 4
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 63 60
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 63 61
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 63 62
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 63 63
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks63_valid : ∀ i, (generatorLeafBlocks63 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks63 i).coordinateU.IsValid ∧
      (generatorLeafBlocks63 i).coordinateV.IsValid ∧
      (generatorLeafBlocks63 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 24⟩
  have hMeta : ∀ i, (generatorLeafBlocks63 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks63 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
