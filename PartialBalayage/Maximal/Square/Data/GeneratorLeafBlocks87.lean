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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 87 of the recorded finite partition. -/
def generatorLeafBlocks87 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 87 0
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 87 1
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 87 2
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 87 3
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 87 4
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 87 5
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 87 6
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 7
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 8
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 87 9
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 87 10
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 11
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 12
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 87 13
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 87 14
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 87 15
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 87 16
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 87 17
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 87 18
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 87 19
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 87 20
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 87 21
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 87 22
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 23
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 24
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 87 25
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 87 26
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 27
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 87 28
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 87 29
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 87 30
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 87 31
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 87 32
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 87 33
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 87 34
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 87 35
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates1 2
    terms := 2
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 87 36
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 87 37
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates1 0
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 87 38
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 87 39
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 87 40
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 87 41
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 87 42
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 87 43
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 87 44
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 87 45
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 87 46
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 87 47
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 87 48
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 87 49
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates23 1
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 87 50
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates23 0
    terms := 1
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 87 51
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates23 1
    terms := 1
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 87 52
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates23 0
    terms := 1
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 87 53
    coordinateU := generatorCoordinates22 1
    coordinateV := generatorCoordinates22 0
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 87 54
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates22 1
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 87 55
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates22 0
    terms := 1
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 87 56
    coordinateU := generatorCoordinates22 1
    coordinateV := generatorCoordinates21 7
    terms := 1
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 87 57
    coordinateU := generatorCoordinates22 1
    coordinateV := generatorCoordinates21 6
    terms := 2
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 87 58
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates21 7
    terms := 0
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 87 59
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates21 6
    terms := 1
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 87 60
    coordinateU := generatorCoordinates21 7
    coordinateV := generatorCoordinates22 1
    terms := 1
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 87 61
    coordinateU := generatorCoordinates21 7
    coordinateV := generatorCoordinates22 0
    terms := 0
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 87 62
    coordinateU := generatorCoordinates21 6
    coordinateV := generatorCoordinates22 1
    terms := 2
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 87 63
    coordinateU := generatorCoordinates21 6
    coordinateV := generatorCoordinates22 0
    terms := 1
    radialRoot := generatorRadialRoots 2 11
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks87_valid : ∀ i, (generatorLeafBlocks87 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks87 i).coordinateU.IsValid ∧
      (generatorLeafBlocks87 i).coordinateV.IsValid ∧
      (generatorLeafBlocks87 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates22_valid 1,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates22_valid 1,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates22_valid 1,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates21_valid 7,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates21_valid 7,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates21_valid 6,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates21_valid 6,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 11⟩
  have hMeta : ∀ i, (generatorLeafBlocks87 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks87 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
