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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates70

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 13 of the recorded finite partition. -/
def generatorLeafBlocks13 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 13 0
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 13 1
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 13 2
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates14 3
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 13 3
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 13 4
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 13 5
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 13 6
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates14 1
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 13 7
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 13 8
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates11 0
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 13 9
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates10 7
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 13 10
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates11 0
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 13 11
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates10 7
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 13 12
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates9 7
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 13 13
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates10 0
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 13 14
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates9 7
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 13 15
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates9 6
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 13 16
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 13 17
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates9 6
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 13 18
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 13 19
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates10 0
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 13 20
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates9 7
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 13 21
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates10 0
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 13 22
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates9 7
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 13 23
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates9 6
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 13 24
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 13 25
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates9 6
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 13 26
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 13 27
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 13 28
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 13 29
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 13 30
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 13 31
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 13 32
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 13 33
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 13 34
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 13 35
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 13 36
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 13 37
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 13 38
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 13 39
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 13 40
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 13 41
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 13 42
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 13 43
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 13 44
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 13 45
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 13 46
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 13 47
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 13 48
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 13 49
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 13 50
    coordinateU := generatorCoordinates71 2
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 13 51
    coordinateU := generatorCoordinates71 2
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 13 52
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 13 53
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 13 54
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 13 55
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 13 56
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 13 57
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 13 58
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 13 59
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 13 60
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 13 61
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 13 62
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 13 63
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks13_valid : ∀ i, (generatorLeafBlocks13 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks13 i).coordinateU.IsValid ∧
      (generatorLeafBlocks13 i).coordinateV.IsValid ∧
      (generatorLeafBlocks13 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates71_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates71_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 46⟩
  have hMeta : ∀ i, (generatorLeafBlocks13 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks13 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
