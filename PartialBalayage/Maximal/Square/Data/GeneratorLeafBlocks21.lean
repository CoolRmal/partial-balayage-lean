/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates62
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates64

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 21 of the recorded finite partition. -/
def generatorLeafBlocks21 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 21 0
    coordinateU := generatorCoordinates62 0
    coordinateV := generatorCoordinates46 1
    terms := 12
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 21 1
    coordinateU := generatorCoordinates62 2
    coordinateV := generatorCoordinates41 4
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 21 2
    coordinateU := generatorCoordinates62 2
    coordinateV := generatorCoordinates41 3
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 21 3
    coordinateU := generatorCoordinates62 1
    coordinateV := generatorCoordinates41 4
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 21 4
    coordinateU := generatorCoordinates62 1
    coordinateV := generatorCoordinates41 3
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 21 5
    coordinateU := generatorCoordinates62 2
    coordinateV := generatorCoordinates36 7
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 21 6
    coordinateU := generatorCoordinates62 2
    coordinateV := generatorCoordinates36 6
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 21 7
    coordinateU := generatorCoordinates62 1
    coordinateV := generatorCoordinates36 7
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 21 8
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 21 9
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates37 0
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 21 10
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 21 11
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates37 0
    terms := 2
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 21 12
    coordinateU := generatorCoordinates62 2
    coordinateV := generatorCoordinates33 0
    terms := 5
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 21 13
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates33 2
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 21 14
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates33 1
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 21 15
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates33 2
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 21 16
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates33 6
    terms := 2
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 21 17
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates33 5
    terms := 4
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 21 18
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates33 6
    terms := 3
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 21 19
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates33 5
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 21 20
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates33 4
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 21 21
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates33 3
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 21 22
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates33 4
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 21 23
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates34 2
    terms := 2
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 21 24
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates34 1
    terms := 3
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 21 25
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates34 2
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 21 26
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates34 1
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 21 27
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates33 2
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 21 28
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates33 6
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 21 29
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 30
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates33 6
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 31
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 21 32
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates34 0
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 21 33
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates33 7
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 34
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates34 0
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 35
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates33 7
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 21 36
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates33 6
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 21 37
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 21 38
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates33 6
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 21 39
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates33 5
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 21 40
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates30 5
    terms := 3
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 21 41
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates30 4
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 21 42
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates30 5
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 21 43
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates30 4
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 21 44
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 21 45
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 46
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 47
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates30 2
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 21 48
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates30 5
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 21 49
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 50
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 21 51
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 21 52
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates30 3
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 21 53
    coordinateU := generatorCoordinates64 4
    coordinateV := generatorCoordinates31 7
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 21 54
    coordinateU := generatorCoordinates64 4
    coordinateV := generatorCoordinates31 6
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 21 55
    coordinateU := generatorCoordinates64 3
    coordinateV := generatorCoordinates31 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 21 56
    coordinateU := generatorCoordinates64 3
    coordinateV := generatorCoordinates31 6
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 21 57
    coordinateU := generatorCoordinates64 2
    coordinateV := generatorCoordinates32 1
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 21 58
    coordinateU := generatorCoordinates64 2
    coordinateV := generatorCoordinates32 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 21 59
    coordinateU := generatorCoordinates64 1
    coordinateV := generatorCoordinates32 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 21 60
    coordinateU := generatorCoordinates64 1
    coordinateV := generatorCoordinates32 0
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 21 61
    coordinateU := generatorCoordinates64 2
    coordinateV := generatorCoordinates31 7
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 21 62
    coordinateU := generatorCoordinates64 2
    coordinateV := generatorCoordinates31 6
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 21 63
    coordinateU := generatorCoordinates64 1
    coordinateV := generatorCoordinates31 7
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks21_valid : ∀ i, (generatorLeafBlocks21 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks21 i).coordinateU.IsValid ∧
      (generatorLeafBlocks21 i).coordinateV.IsValid ∧
      (generatorLeafBlocks21 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates62_valid 0,
        generatorCoordinates46_valid 1, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates62_valid 2,
        generatorCoordinates41_valid 4, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates62_valid 2,
        generatorCoordinates41_valid 3, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates62_valid 1,
        generatorCoordinates41_valid 4, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates62_valid 1,
        generatorCoordinates41_valid 3, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates62_valid 2,
        generatorCoordinates36_valid 7, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates62_valid 2,
        generatorCoordinates36_valid 6, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates62_valid 1,
        generatorCoordinates36_valid 7, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates62_valid 2,
        generatorCoordinates33_valid 0, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates33_valid 4, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates33_valid 4, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates64_valid 4,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates64_valid 4,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates64_valid 3,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates64_valid 3,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates64_valid 2,
        generatorCoordinates32_valid 1, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates64_valid 2,
        generatorCoordinates32_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates64_valid 1,
        generatorCoordinates32_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates64_valid 1,
        generatorCoordinates32_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates64_valid 2,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates64_valid 2,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates64_valid 1,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 4 60⟩
  have hMeta : ∀ i, (generatorLeafBlocks21 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks21 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
