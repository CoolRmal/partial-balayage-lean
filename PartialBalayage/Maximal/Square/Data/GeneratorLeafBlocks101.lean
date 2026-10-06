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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates12
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates16

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 101 of the recorded finite partition. -/
def generatorLeafBlocks101 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 101 0
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 101 1
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 101 2
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 101 3
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 101 4
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates1 3
    terms := 1
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 5
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates1 4
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 6
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 101 7
    coordinateU := generatorCoordinates16 3
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 46
  },
  {
    rectangle := generatorPartitionRectangles 101 8
    coordinateU := generatorCoordinates16 3
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 101 9
    coordinateU := generatorCoordinates16 2
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 101 10
    coordinateU := generatorCoordinates16 2
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 44
  },
  {
    rectangle := generatorPartitionRectangles 101 11
    coordinateU := generatorCoordinates16 3
    coordinateV := generatorCoordinates2 4
    terms := 1
    radialRoot := generatorRadialRoots 0 44
  },
  {
    rectangle := generatorPartitionRectangles 101 12
    coordinateU := generatorCoordinates16 3
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 13
    coordinateU := generatorCoordinates16 2
    coordinateV := generatorCoordinates2 4
    terms := 1
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 14
    coordinateU := generatorCoordinates16 2
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 42
  },
  {
    rectangle := generatorPartitionRectangles 101 15
    coordinateU := generatorCoordinates16 1
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 44
  },
  {
    rectangle := generatorPartitionRectangles 101 16
    coordinateU := generatorCoordinates16 1
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 17
    coordinateU := generatorCoordinates16 0
    coordinateV := generatorCoordinates2 6
    terms := 1
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 18
    coordinateU := generatorCoordinates16 0
    coordinateV := generatorCoordinates2 5
    terms := 1
    radialRoot := generatorRadialRoots 0 42
  },
  {
    rectangle := generatorPartitionRectangles 101 19
    coordinateU := generatorCoordinates16 1
    coordinateV := generatorCoordinates2 4
    terms := 1
    radialRoot := generatorRadialRoots 0 42
  },
  {
    rectangle := generatorPartitionRectangles 101 20
    coordinateU := generatorCoordinates16 1
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 101 21
    coordinateU := generatorCoordinates16 0
    coordinateV := generatorCoordinates2 4
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 101 22
    coordinateU := generatorCoordinates16 0
    coordinateV := generatorCoordinates2 3
    terms := 0
    radialRoot := generatorRadialRoots 0 40
  },
  {
    rectangle := generatorPartitionRectangles 101 23
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 101 24
    coordinateU := generatorCoordinates14 7
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 101 25
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 101 26
    coordinateU := generatorCoordinates14 6
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 101 27
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 101 28
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 101 29
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 101 30
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 101 31
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 36
  },
  {
    rectangle := generatorPartitionRectangles 101 32
    coordinateU := generatorCoordinates14 5
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 101 33
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 101 34
    coordinateU := generatorCoordinates14 4
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 31
  },
  {
    rectangle := generatorPartitionRectangles 101 35
    coordinateU := generatorCoordinates9 4
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 101 36
    coordinateU := generatorCoordinates9 4
    coordinateV := generatorCoordinates9 3
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 101 37
    coordinateU := generatorCoordinates9 3
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 101 38
    coordinateU := generatorCoordinates9 3
    coordinateV := generatorCoordinates9 3
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 101 39
    coordinateU := generatorCoordinates10 0
    coordinateV := generatorCoordinates5 5
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 101 40
    coordinateU := generatorCoordinates10 0
    coordinateV := generatorCoordinates5 4
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 101 41
    coordinateU := generatorCoordinates9 7
    coordinateV := generatorCoordinates5 5
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 101 42
    coordinateU := generatorCoordinates9 7
    coordinateV := generatorCoordinates5 4
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 101 43
    coordinateU := generatorCoordinates10 0
    coordinateV := generatorCoordinates5 3
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 101 44
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 101 45
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 101 46
    coordinateU := generatorCoordinates10 7
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 101 47
    coordinateU := generatorCoordinates10 7
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 101 48
    coordinateU := generatorCoordinates9 7
    coordinateV := generatorCoordinates5 3
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 101 49
    coordinateU := generatorCoordinates10 6
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 101 50
    coordinateU := generatorCoordinates10 6
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 51
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 52
    coordinateU := generatorCoordinates10 5
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 101 53
    coordinateU := generatorCoordinates9 3
    coordinateV := generatorCoordinates5 1
    terms := 0
    radialRoot := generatorRadialRoots 0 47
  },
  {
    rectangle := generatorPartitionRectangles 101 54
    coordinateU := generatorCoordinates9 6
    coordinateV := generatorCoordinates5 3
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 55
    coordinateU := generatorCoordinates9 6
    coordinateV := generatorCoordinates5 2
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 101 56
    coordinateU := generatorCoordinates9 5
    coordinateV := generatorCoordinates5 3
    terms := 0
    radialRoot := generatorRadialRoots 0 39
  },
  {
    rectangle := generatorPartitionRectangles 101 57
    coordinateU := generatorCoordinates9 5
    coordinateV := generatorCoordinates5 2
    terms := 0
    radialRoot := generatorRadialRoots 0 33
  },
  {
    rectangle := generatorPartitionRectangles 101 58
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 45
  },
  {
    rectangle := generatorPartitionRectangles 101 59
    coordinateU := generatorCoordinates11 0
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 60
    coordinateU := generatorCoordinates10 7
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 43
  },
  {
    rectangle := generatorPartitionRectangles 101 61
    coordinateU := generatorCoordinates10 7
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  },
  {
    rectangle := generatorPartitionRectangles 101 62
    coordinateU := generatorCoordinates12 6
    coordinateV := generatorCoordinates3 2
    terms := 0
    radialRoot := generatorRadialRoots 0 42
  },
  {
    rectangle := generatorPartitionRectangles 101 63
    coordinateU := generatorCoordinates12 6
    coordinateV := generatorCoordinates3 1
    terms := 0
    radialRoot := generatorRadialRoots 0 41
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks101_valid : ∀ i, (generatorLeafBlocks101 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks101 i).coordinateU.IsValid ∧
      (generatorLeafBlocks101 i).coordinateV.IsValid ∧
      (generatorLeafBlocks101 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates16_valid 3,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 46⟩
    · exact ⟨generatorCoordinates16_valid 3,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates16_valid 2,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates16_valid 2,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 44⟩
    · exact ⟨generatorCoordinates16_valid 3,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 44⟩
    · exact ⟨generatorCoordinates16_valid 3,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates16_valid 2,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates16_valid 2,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 42⟩
    · exact ⟨generatorCoordinates16_valid 1,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 44⟩
    · exact ⟨generatorCoordinates16_valid 1,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates16_valid 0,
        generatorCoordinates2_valid 6, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates16_valid 0,
        generatorCoordinates2_valid 5, generatorRadialRoots_valid 0 42⟩
    · exact ⟨generatorCoordinates16_valid 1,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 42⟩
    · exact ⟨generatorCoordinates16_valid 1,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates16_valid 0,
        generatorCoordinates2_valid 4, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates16_valid 0,
        generatorCoordinates2_valid 3, generatorRadialRoots_valid 0 40⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates14_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates14_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 36⟩
    · exact ⟨generatorCoordinates14_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates14_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 31⟩
    · exact ⟨generatorCoordinates9_valid 4,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates9_valid 4,
        generatorCoordinates9_valid 3, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates9_valid 3,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates9_valid 3,
        generatorCoordinates9_valid 3, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates10_valid 0,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates10_valid 0,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates9_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates9_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates10_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates10_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates10_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates9_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates10_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates10_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates10_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates9_valid 3,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 0 47⟩
    · exact ⟨generatorCoordinates9_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates9_valid 6,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates9_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 0 39⟩
    · exact ⟨generatorCoordinates9_valid 5,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 0 33⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 45⟩
    · exact ⟨generatorCoordinates11_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates10_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 43⟩
    · exact ⟨generatorCoordinates10_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 41⟩
    · exact ⟨generatorCoordinates12_valid 6,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 42⟩
    · exact ⟨generatorCoordinates12_valid 6,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 41⟩
  have hMeta : ∀ i, (generatorLeafBlocks101 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks101 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
