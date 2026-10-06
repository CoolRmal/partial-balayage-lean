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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates7
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 103 of the recorded finite partition. -/
def generatorLeafBlocks103 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 103 0
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 103 1
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 103 2
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 103 3
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates1 3
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 4
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 5
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates1 3
    terms := 0
    radialRoot := generatorRadialRoots 0 28
  },
  {
    rectangle := generatorPartitionRectangles 103 6
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 103 7
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 8
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 9
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 28
  },
  {
    rectangle := generatorPartitionRectangles 103 10
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 28
  },
  {
    rectangle := generatorPartitionRectangles 103 11
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates1 3
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 103 12
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 103 13
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates1 3
    terms := 0
    radialRoot := generatorRadialRoots 0 26
  },
  {
    rectangle := generatorPartitionRectangles 103 14
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 28
  },
  {
    rectangle := generatorPartitionRectangles 103 15
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 103 16
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 103 17
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 26
  },
  {
    rectangle := generatorPartitionRectangles 103 18
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 26
  },
  {
    rectangle := generatorPartitionRectangles 103 19
    coordinateU := generatorCoordinates10 4
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 20
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 21
    coordinateU := generatorCoordinates10 3
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 24
  },
  {
    rectangle := generatorPartitionRectangles 103 22
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 26
  },
  {
    rectangle := generatorPartitionRectangles 103 23
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 24
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 25
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 24
  },
  {
    rectangle := generatorPartitionRectangles 103 26
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 24
  },
  {
    rectangle := generatorPartitionRectangles 103 27
    coordinateU := generatorCoordinates10 2
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 22
  },
  {
    rectangle := generatorPartitionRectangles 103 28
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 22
  },
  {
    rectangle := generatorPartitionRectangles 103 29
    coordinateU := generatorCoordinates10 1
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 20
  },
  {
    rectangle := generatorPartitionRectangles 103 30
    coordinateU := generatorCoordinates5 1
    coordinateV := generatorCoordinates5 1
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 103 31
    coordinateU := generatorCoordinates5 5
    coordinateV := generatorCoordinates5 3
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 103 32
    coordinateU := generatorCoordinates5 5
    coordinateV := generatorCoordinates5 2
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 33
    coordinateU := generatorCoordinates5 4
    coordinateV := generatorCoordinates5 3
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 34
    coordinateU := generatorCoordinates5 4
    coordinateV := generatorCoordinates5 2
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 103 35
    coordinateU := generatorCoordinates5 3
    coordinateV := generatorCoordinates5 5
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 103 36
    coordinateU := generatorCoordinates5 3
    coordinateV := generatorCoordinates5 4
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 37
    coordinateU := generatorCoordinates5 2
    coordinateV := generatorCoordinates5 5
    terms := 0
    radialRoot := generatorRadialRoots 0 29
  },
  {
    rectangle := generatorPartitionRectangles 103 38
    coordinateU := generatorCoordinates5 2
    coordinateV := generatorCoordinates5 4
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 103 39
    coordinateU := generatorCoordinates5 0
    coordinateV := generatorCoordinates5 0
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 40
    coordinateU := generatorCoordinates5 5
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 27
  },
  {
    rectangle := generatorPartitionRectangles 103 41
    coordinateU := generatorCoordinates6 5
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 26
  },
  {
    rectangle := generatorPartitionRectangles 103 42
    coordinateU := generatorCoordinates6 5
    coordinateV := generatorCoordinates1 3
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 43
    coordinateU := generatorCoordinates6 4
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 44
    coordinateU := generatorCoordinates6 4
    coordinateV := generatorCoordinates1 3
    terms := 0
    radialRoot := generatorRadialRoots 0 24
  },
  {
    rectangle := generatorPartitionRectangles 103 45
    coordinateU := generatorCoordinates5 4
    coordinateV := generatorCoordinates0 6
    terms := 0
    radialRoot := generatorRadialRoots 0 25
  },
  {
    rectangle := generatorPartitionRectangles 103 46
    coordinateU := generatorCoordinates5 4
    coordinateV := generatorCoordinates0 5
    terms := 0
    radialRoot := generatorRadialRoots 0 22
  },
  {
    rectangle := generatorPartitionRectangles 103 47
    coordinateU := generatorCoordinates6 5
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 24
  },
  {
    rectangle := generatorPartitionRectangles 103 48
    coordinateU := generatorCoordinates7 7
    coordinateV := generatorCoordinates2 4
    terms := 0
    radialRoot := generatorRadialRoots 0 23
  },
  {
    rectangle := generatorPartitionRectangles 103 49
    coordinateU := generatorCoordinates7 7
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 22
  },
  {
    rectangle := generatorPartitionRectangles 103 50
    coordinateU := generatorCoordinates7 6
    coordinateV := generatorCoordinates2 4
    terms := 0
    radialRoot := generatorRadialRoots 0 22
  },
  {
    rectangle := generatorPartitionRectangles 103 51
    coordinateU := generatorCoordinates7 6
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 21
  },
  {
    rectangle := generatorPartitionRectangles 103 52
    coordinateU := generatorCoordinates6 4
    coordinateV := generatorCoordinates1 2
    terms := 0
    radialRoot := generatorRadialRoots 0 22
  },
  {
    rectangle := generatorPartitionRectangles 103 53
    coordinateU := generatorCoordinates7 5
    coordinateV := generatorCoordinates2 4
    terms := 0
    radialRoot := generatorRadialRoots 0 21
  },
  {
    rectangle := generatorPartitionRectangles 103 54
    coordinateU := generatorCoordinates7 5
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 20
  },
  {
    rectangle := generatorPartitionRectangles 103 55
    coordinateU := generatorCoordinates7 4
    coordinateV := generatorCoordinates2 4
    terms := 0
    radialRoot := generatorRadialRoots 0 20
  },
  {
    rectangle := generatorPartitionRectangles 103 56
    coordinateU := generatorCoordinates7 4
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 19
  },
  {
    rectangle := generatorPartitionRectangles 103 57
    coordinateU := generatorCoordinates7 7
    coordinateV := generatorCoordinates2 2
    terms := 0
    radialRoot := generatorRadialRoots 0 21
  },
  {
    rectangle := generatorPartitionRectangles 103 58
    coordinateU := generatorCoordinates7 7
    coordinateV := generatorCoordinates2 1
    terms := 0
    radialRoot := generatorRadialRoots 0 20
  },
  {
    rectangle := generatorPartitionRectangles 103 59
    coordinateU := generatorCoordinates7 6
    coordinateV := generatorCoordinates2 2
    terms := 0
    radialRoot := generatorRadialRoots 0 20
  },
  {
    rectangle := generatorPartitionRectangles 103 60
    coordinateU := generatorCoordinates7 6
    coordinateV := generatorCoordinates2 1
    terms := 0
    radialRoot := generatorRadialRoots 0 19
  },
  {
    rectangle := generatorPartitionRectangles 103 61
    coordinateU := generatorCoordinates7 7
    coordinateV := generatorCoordinates2 0
    terms := 0
    radialRoot := generatorRadialRoots 0 19
  },
  {
    rectangle := generatorPartitionRectangles 103 62
    coordinateU := generatorCoordinates7 7
    coordinateV := generatorCoordinates1 7
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  },
  {
    rectangle := generatorPartitionRectangles 103 63
    coordinateU := generatorCoordinates7 6
    coordinateV := generatorCoordinates2 0
    terms := 0
    radialRoot := generatorRadialRoots 0 17
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks103_valid : ∀ i, (generatorLeafBlocks103 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks103 i).coordinateU.IsValid ∧
      (generatorLeafBlocks103 i).coordinateV.IsValid ∧
      (generatorLeafBlocks103 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 28⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 28⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 28⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 26⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 28⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 26⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 26⟩
    · exact ⟨generatorCoordinates10_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates10_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 24⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 26⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 24⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 24⟩
    · exact ⟨generatorCoordinates10_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 22⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 22⟩
    · exact ⟨generatorCoordinates10_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 20⟩
    · exact ⟨generatorCoordinates5_valid 1,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates5_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates5_valid 5,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates5_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates5_valid 4,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates5_valid 3,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates5_valid 3,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates5_valid 2,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 0 29⟩
    · exact ⟨generatorCoordinates5_valid 2,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates5_valid 0,
        generatorCoordinates5_valid 0, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates5_valid 5,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 27⟩
    · exact ⟨generatorCoordinates6_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 26⟩
    · exact ⟨generatorCoordinates6_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates6_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates6_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 24⟩
    · exact ⟨generatorCoordinates5_valid 4,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 0 25⟩
    · exact ⟨generatorCoordinates5_valid 4,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 0 22⟩
    · exact ⟨generatorCoordinates6_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 24⟩
    · exact ⟨generatorCoordinates7_valid 7,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 23⟩
    · exact ⟨generatorCoordinates7_valid 7,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 22⟩
    · exact ⟨generatorCoordinates7_valid 6,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 22⟩
    · exact ⟨generatorCoordinates7_valid 6,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 21⟩
    · exact ⟨generatorCoordinates6_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 22⟩
    · exact ⟨generatorCoordinates7_valid 5,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 21⟩
    · exact ⟨generatorCoordinates7_valid 5,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 20⟩
    · exact ⟨generatorCoordinates7_valid 4,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 20⟩
    · exact ⟨generatorCoordinates7_valid 4,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 19⟩
    · exact ⟨generatorCoordinates7_valid 7,
        generatorCoordinates2_valid 2, generatorRadialRoots_valid 0 21⟩
    · exact ⟨generatorCoordinates7_valid 7,
        generatorCoordinates2_valid 1, generatorRadialRoots_valid 0 20⟩
    · exact ⟨generatorCoordinates7_valid 6,
        generatorCoordinates2_valid 2, generatorRadialRoots_valid 0 20⟩
    · exact ⟨generatorCoordinates7_valid 6,
        generatorCoordinates2_valid 1, generatorRadialRoots_valid 0 19⟩
    · exact ⟨generatorCoordinates7_valid 7,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 0 19⟩
    · exact ⟨generatorCoordinates7_valid 7,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 0 17⟩
    · exact ⟨generatorCoordinates7_valid 6,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 0 17⟩
  have hMeta : ∀ i, (generatorLeafBlocks103 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks103 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
