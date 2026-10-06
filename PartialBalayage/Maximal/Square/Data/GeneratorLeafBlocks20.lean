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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates62
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates64
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates66

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 20 of the recorded finite partition. -/
def generatorLeafBlocks20 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 20 0
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 20 1
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 20 2
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 20 3
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 20 4
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 20 5
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 20 6
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 20 7
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 20 8
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 20 9
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 20 10
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 20 11
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 20 12
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 20 13
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 20 14
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 20 15
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 20 16
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 20 17
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 20 18
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 20 19
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 20 20
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 20 21
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 20 22
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 20 23
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 20 24
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 20 25
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 20 26
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 20 27
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 20 28
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 20 29
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 20 30
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 20 31
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 20 32
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 20 33
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 20 34
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 20 35
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 20 36
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 20 37
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 20 38
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 20 39
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 20 40
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 20 41
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 20 42
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 20 43
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 20 44
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 20 45
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 20 46
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 20 47
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 20 48
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 20 49
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 20 50
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 20 51
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 20 52
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 20 53
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 20 54
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 20 55
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 20 56
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates1 2
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 20 57
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates1 1
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 20 58
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates1 2
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 20 59
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates1 1
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 20 60
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 20 61
    coordinateU := generatorCoordinates62 2
    coordinateV := generatorCoordinates50 6
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 20 62
    coordinateU := generatorCoordinates62 1
    coordinateV := generatorCoordinates50 7
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 20 63
    coordinateU := generatorCoordinates62 1
    coordinateV := generatorCoordinates50 6
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks20_valid : ∀ i, (generatorLeafBlocks20 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks20 i).coordinateU.IsValid ∧
      (generatorLeafBlocks20 i).coordinateV.IsValid ∧
      (generatorLeafBlocks20 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates62_valid 2,
        generatorCoordinates50_valid 6, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates62_valid 1,
        generatorCoordinates50_valid 7, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates62_valid 1,
        generatorCoordinates50_valid 6, generatorRadialRoots_valid 5 47⟩
  have hMeta : ∀ i, (generatorLeafBlocks20 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks20 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
