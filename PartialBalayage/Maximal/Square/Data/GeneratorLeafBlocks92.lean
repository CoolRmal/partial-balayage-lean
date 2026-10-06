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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates2
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates3
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates24

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 92 of the recorded finite partition. -/
def generatorLeafBlocks92 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 92 0
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 92 1
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 92 2
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 92 3
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 92 4
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates6 5
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 92 5
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates6 4
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 92 6
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates6 5
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 92 7
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates6 4
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 92 8
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates6 3
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 92 9
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 92 10
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates6 3
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 92 11
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 92 12
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 92 13
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 92 14
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 92 15
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 92 16
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 92 17
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 18
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 19
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 92 20
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 92 21
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 22
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 23
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 92 24
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 92 25
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 92 26
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 92 27
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 92 28
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 92 29
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 92 30
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 92 31
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 92 32
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 92 33
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 34
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 35
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 92 36
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 92 37
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 38
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 92 39
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 92 40
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 92 41
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 92 42
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 92 43
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates3 0
    terms := 2
    radialRoot := generatorRadialRoots 1 18
  },
  {
    rectangle := generatorPartitionRectangles 92 44
    coordinateU := generatorCoordinates24 1
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 92 45
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates3 0
    terms := 2
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 92 46
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 16
  },
  {
    rectangle := generatorPartitionRectangles 92 47
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 92 48
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 92 49
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 92 50
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 92 51
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 92 52
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 92 53
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 92 54
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 92 55
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 92 56
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 92 57
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 92 58
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 92 59
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 92 60
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 92 61
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 92 62
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 92 63
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks92_valid : ∀ i, (generatorLeafBlocks92 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks92 i).coordinateU.IsValid ∧
      (generatorLeafBlocks92 i).coordinateV.IsValid ∧
      (generatorLeafBlocks92 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 18⟩
    · exact ⟨generatorCoordinates24_valid 1,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 16⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 20⟩
  have hMeta : ∀ i, (generatorLeafBlocks92 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks92 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
