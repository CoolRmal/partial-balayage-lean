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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 68 of the recorded finite partition. -/
def generatorLeafBlocks68 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 68 0
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 68 1
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 68 2
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 68 3
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 68 4
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 68 5
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 68 6
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 68 7
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 68 8
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 68 9
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 68 10
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 68 11
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 68 12
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 68 13
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 68 14
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 68 15
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 68 16
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 68 17
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 68 18
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 68 19
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 68 20
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 68 21
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates1 1
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 68 22
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 68 23
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 68 24
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 68 25
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates0 7
    terms := 1
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 68 26
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates34 4
    terms := 5
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 68 27
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates34 3
    terms := 4
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 68 28
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates34 4
    terms := 4
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 68 29
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates34 3
    terms := 3
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 68 30
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates34 2
    terms := 4
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 68 31
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates34 1
    terms := 4
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 68 32
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates34 2
    terms := 3
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 68 33
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates34 1
    terms := 3
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 68 34
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates34 4
    terms := 4
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 68 35
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates34 3
    terms := 3
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 68 36
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates34 4
    terms := 4
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 68 37
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates34 3
    terms := 3
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 68 38
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates33 3
    terms := 3
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 68 39
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates34 0
    terms := 4
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 68 40
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates33 7
    terms := 5
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 68 41
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates34 0
    terms := 3
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 68 42
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates33 7
    terms := 3
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 68 43
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates33 6
    terms := 5
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 68 44
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 68 45
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 68 46
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates33 5
    terms := 4
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 68 47
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates33 2
    terms := 3
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 68 48
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates33 1
    terms := 4
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 68 49
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates34 4
    terms := 4
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 68 50
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates34 3
    terms := 3
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 68 51
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates34 4
    terms := 5
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 68 52
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates34 3
    terms := 3
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 68 53
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates33 3
    terms := 3
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 68 54
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates34 4
    terms := 5
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 68 55
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates34 3
    terms := 4
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 68 56
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates34 4
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 68 57
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates34 3
    terms := 4
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 68 58
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates33 3
    terms := 4
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 68 59
    coordinateU := generatorCoordinates32 7
    coordinateV := generatorCoordinates32 7
    terms := 3
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 68 60
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 68 61
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 68 62
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates30 5
    terms := 4
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 68 63
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates30 4
    terms := 5
    radialRoot := generatorRadialRoots 3 20
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks68_valid : ∀ i, (generatorLeafBlocks68 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks68 i).coordinateU.IsValid ∧
      (generatorLeafBlocks68 i).coordinateV.IsValid ∧
      (generatorLeafBlocks68 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates32_valid 7,
        generatorCoordinates32_valid 7, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 3 20⟩
  have hMeta : ∀ i, (generatorLeafBlocks68 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks68 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
