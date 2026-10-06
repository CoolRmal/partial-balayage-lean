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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates3
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates76
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates78
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates80
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates82

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 3 of the recorded finite partition. -/
def generatorLeafBlocks3 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 3 0
    coordinateU := generatorCoordinates82 3
    coordinateV := generatorCoordinates3 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 3 1
    coordinateU := generatorCoordinates82 2
    coordinateV := generatorCoordinates3 2
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 3 2
    coordinateU := generatorCoordinates82 2
    coordinateV := generatorCoordinates3 1
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 3 3
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates1 3
    terms := 50
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 3 4
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates1 4
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 3 5
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates1 3
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 3 6
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 3 7
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 3 8
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 3 9
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 3 10
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates1 4
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 3 11
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates1 3
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 3 12
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates1 4
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 3 13
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates1 3
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 3 14
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 3 15
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates1 1
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 3 16
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 3 17
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates1 1
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 3 18
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates1 0
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 3 19
    coordinateU := generatorCoordinates81 5
    coordinateV := generatorCoordinates0 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 3 20
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates1 0
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 3 21
    coordinateU := generatorCoordinates81 4
    coordinateV := generatorCoordinates0 7
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 3 22
    coordinateU := generatorCoordinates80 6
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 3 23
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates1 0
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 3 24
    coordinateU := generatorCoordinates81 3
    coordinateV := generatorCoordinates0 7
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 3 25
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 3 26
    coordinateU := generatorCoordinates81 2
    coordinateV := generatorCoordinates0 7
    terms := 20
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 3 27
    coordinateU := generatorCoordinates78 0
    coordinateV := generatorCoordinates25 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 3 28
    coordinateU := generatorCoordinates77 7
    coordinateV := generatorCoordinates25 2
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 3 29
    coordinateU := generatorCoordinates77 7
    coordinateV := generatorCoordinates25 1
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 3 30
    coordinateU := generatorCoordinates77 6
    coordinateV := generatorCoordinates21 3
    terms := 8
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 3 31
    coordinateU := generatorCoordinates78 0
    coordinateV := generatorCoordinates18 2
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 3 32
    coordinateU := generatorCoordinates78 0
    coordinateV := generatorCoordinates18 1
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 3 33
    coordinateU := generatorCoordinates77 7
    coordinateV := generatorCoordinates18 2
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 3 34
    coordinateU := generatorCoordinates77 7
    coordinateV := generatorCoordinates18 1
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 3 35
    coordinateU := generatorCoordinates78 0
    coordinateV := generatorCoordinates13 7
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 3 36
    coordinateU := generatorCoordinates78 0
    coordinateV := generatorCoordinates13 6
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 3 37
    coordinateU := generatorCoordinates77 7
    coordinateV := generatorCoordinates13 7
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 3 38
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 3 39
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates14 0
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 3 40
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 3 41
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates14 0
    terms := 3
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 3 42
    coordinateU := generatorCoordinates78 0
    coordinateV := generatorCoordinates9 4
    terms := 8
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 3 43
    coordinateU := generatorCoordinates78 4
    coordinateV := generatorCoordinates9 6
    terms := 2
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 3 44
    coordinateU := generatorCoordinates78 4
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 3 45
    coordinateU := generatorCoordinates78 3
    coordinateV := generatorCoordinates9 6
    terms := 4
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 3 46
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates10 2
    terms := 4
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 3 47
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates10 1
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 3 48
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates10 2
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 3 49
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates10 1
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 3 50
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates10 0
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 3 51
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates9 7
    terms := 3
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 3 52
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 3 53
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates10 6
    terms := 3
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 3 54
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates10 5
    terms := 4
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 3 55
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates10 6
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 3 56
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates10 5
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 3 57
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 3 58
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates10 2
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 3 59
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates10 1
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 3 60
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates10 2
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 3 61
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates10 1
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 3 62
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates10 4
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 3 63
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates10 3
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks3_valid : ∀ i, (generatorLeafBlocks3 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks3 i).coordinateU.IsValid ∧
      (generatorLeafBlocks3 i).coordinateV.IsValid ∧
      (generatorLeafBlocks3 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates82_valid 3,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates82_valid 2,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates82_valid 2,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates81_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates81_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates80_valid 6,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates81_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates81_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates78_valid 0,
        generatorCoordinates25_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates77_valid 7,
        generatorCoordinates25_valid 2, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates77_valid 7,
        generatorCoordinates25_valid 1, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates77_valid 6,
        generatorCoordinates21_valid 3, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates78_valid 0,
        generatorCoordinates18_valid 2, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates78_valid 0,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates77_valid 7,
        generatorCoordinates18_valid 2, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates77_valid 7,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates78_valid 0,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates78_valid 0,
        generatorCoordinates13_valid 6, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates77_valid 7,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates78_valid 0,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates78_valid 4,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates78_valid 4,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates78_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 5 2⟩
  have hMeta : ∀ i, (generatorLeafBlocks3 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks3 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
