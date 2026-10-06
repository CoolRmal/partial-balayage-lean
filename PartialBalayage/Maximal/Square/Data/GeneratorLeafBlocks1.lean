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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates80
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates82
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates84
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates86

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 1 of the recorded finite partition. -/
def generatorLeafBlocks1 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 1 0
    coordinateU := generatorCoordinates84 4
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 1 1
    coordinateU := generatorCoordinates85 4
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 11
  },
  {
    rectangle := generatorPartitionRectangles 1 2
    coordinateU := generatorCoordinates86 6
    coordinateV := generatorCoordinates3 6
    terms := 30
    radialRoot := generatorRadialRoots 5 10
  },
  {
    rectangle := generatorPartitionRectangles 1 3
    coordinateU := generatorCoordinates86 6
    coordinateV := generatorCoordinates3 5
    terms := 30
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 4
    coordinateU := generatorCoordinates86 5
    coordinateV := generatorCoordinates3 6
    terms := 30
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 5
    coordinateU := generatorCoordinates86 5
    coordinateV := generatorCoordinates3 5
    terms := 50
    radialRoot := generatorRadialRoots 5 8
  },
  {
    rectangle := generatorPartitionRectangles 1 6
    coordinateU := generatorCoordinates85 3
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 7
    coordinateU := generatorCoordinates86 4
    coordinateV := generatorCoordinates3 6
    terms := 30
    radialRoot := generatorRadialRoots 5 8
  },
  {
    rectangle := generatorPartitionRectangles 1 8
    coordinateU := generatorCoordinates86 4
    coordinateV := generatorCoordinates3 5
    terms := 50
    radialRoot := generatorRadialRoots 5 7
  },
  {
    rectangle := generatorPartitionRectangles 1 9
    coordinateU := generatorCoordinates86 3
    coordinateV := generatorCoordinates3 6
    terms := 30
    radialRoot := generatorRadialRoots 5 7
  },
  {
    rectangle := generatorPartitionRectangles 1 10
    coordinateU := generatorCoordinates86 3
    coordinateV := generatorCoordinates3 5
    terms := 50
    radialRoot := generatorRadialRoots 5 6
  },
  {
    rectangle := generatorPartitionRectangles 1 11
    coordinateU := generatorCoordinates84 3
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 12
    coordinateU := generatorCoordinates85 2
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 7
  },
  {
    rectangle := generatorPartitionRectangles 1 13
    coordinateU := generatorCoordinates86 2
    coordinateV := generatorCoordinates3 6
    terms := 30
    radialRoot := generatorRadialRoots 5 6
  },
  {
    rectangle := generatorPartitionRectangles 1 14
    coordinateU := generatorCoordinates86 2
    coordinateV := generatorCoordinates3 5
    terms := 30
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 1 15
    coordinateU := generatorCoordinates86 1
    coordinateV := generatorCoordinates3 6
    terms := 30
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 1 16
    coordinateU := generatorCoordinates86 1
    coordinateV := generatorCoordinates3 5
    terms := 30
    radialRoot := generatorRadialRoots 5 4
  },
  {
    rectangle := generatorPartitionRectangles 1 17
    coordinateU := generatorCoordinates85 1
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 1 18
    coordinateU := generatorCoordinates85 1
    coordinateV := generatorCoordinates1 7
    terms := 50
    radialRoot := generatorRadialRoots 5 3
  },
  {
    rectangle := generatorPartitionRectangles 1 19
    coordinateU := generatorCoordinates83 4
    coordinateV := generatorCoordinates0 6
    terms := 5
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 1 20
    coordinateU := generatorCoordinates83 4
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 1 21
    coordinateU := generatorCoordinates84 0
    coordinateV := generatorCoordinates1 6
    terms := 4
    radialRoot := generatorRadialRoots 5 17
  },
  {
    rectangle := generatorPartitionRectangles 1 22
    coordinateU := generatorCoordinates84 0
    coordinateV := generatorCoordinates1 5
    terms := 5
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 1 23
    coordinateU := generatorCoordinates83 7
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 1 24
    coordinateU := generatorCoordinates83 7
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 1 25
    coordinateU := generatorCoordinates84 0
    coordinateV := generatorCoordinates1 4
    terms := 8
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 1 26
    coordinateU := generatorCoordinates84 0
    coordinateV := generatorCoordinates1 3
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 27
    coordinateU := generatorCoordinates83 7
    coordinateV := generatorCoordinates1 4
    terms := 12
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 28
    coordinateU := generatorCoordinates83 7
    coordinateV := generatorCoordinates1 3
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 1 29
    coordinateU := generatorCoordinates83 4
    coordinateV := generatorCoordinates0 4
    terms := 30
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 30
    coordinateU := generatorCoordinates84 2
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 1 31
    coordinateU := generatorCoordinates85 0
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 3
  },
  {
    rectangle := generatorPartitionRectangles 1 32
    coordinateU := generatorCoordinates85 0
    coordinateV := generatorCoordinates1 7
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 1 33
    coordinateU := generatorCoordinates84 7
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 1 34
    coordinateU := generatorCoordinates84 7
    coordinateV := generatorCoordinates1 7
    terms := 20
    radialRoot := generatorRadialRoots 5 1
  },
  {
    rectangle := generatorPartitionRectangles 1 35
    coordinateU := generatorCoordinates84 1
    coordinateV := generatorCoordinates1 0
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 1 36
    coordinateU := generatorCoordinates84 1
    coordinateV := generatorCoordinates0 7
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 1 37
    coordinateU := generatorCoordinates83 3
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 1 38
    coordinateU := generatorCoordinates83 3
    coordinateV := generatorCoordinates0 3
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 1 39
    coordinateU := generatorCoordinates80 5
    coordinateV := generatorCoordinates21 4
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 1 40
    coordinateU := generatorCoordinates80 4
    coordinateV := generatorCoordinates21 5
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 1 41
    coordinateU := generatorCoordinates80 4
    coordinateV := generatorCoordinates21 4
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 1 42
    coordinateU := generatorCoordinates80 3
    coordinateV := generatorCoordinates18 0
    terms := 8
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 1 43
    coordinateU := generatorCoordinates80 5
    coordinateV := generatorCoordinates13 7
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 1 44
    coordinateU := generatorCoordinates80 5
    coordinateV := generatorCoordinates13 6
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 1 45
    coordinateU := generatorCoordinates80 4
    coordinateV := generatorCoordinates13 7
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 1 46
    coordinateU := generatorCoordinates80 4
    coordinateV := generatorCoordinates13 6
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 1 47
    coordinateU := generatorCoordinates80 5
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 1 48
    coordinateU := generatorCoordinates80 5
    coordinateV := generatorCoordinates9 3
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 1 49
    coordinateU := generatorCoordinates80 4
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 1 50
    coordinateU := generatorCoordinates80 7
    coordinateV := generatorCoordinates9 6
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 1 51
    coordinateU := generatorCoordinates80 7
    coordinateV := generatorCoordinates9 5
    terms := 1
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 1 52
    coordinateU := generatorCoordinates80 6
    coordinateV := generatorCoordinates9 6
    terms := 1
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 1 53
    coordinateU := generatorCoordinates80 6
    coordinateV := generatorCoordinates9 5
    terms := 3
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 1 54
    coordinateU := generatorCoordinates80 5
    coordinateV := generatorCoordinates5 1
    terms := 20
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 1 55
    coordinateU := generatorCoordinates81 1
    coordinateV := generatorCoordinates5 3
    terms := 3
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 1 56
    coordinateU := generatorCoordinates82 1
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 5 17
  },
  {
    rectangle := generatorPartitionRectangles 1 57
    coordinateU := generatorCoordinates82 1
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 1 58
    coordinateU := generatorCoordinates82 0
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 1 59
    coordinateU := generatorCoordinates82 0
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 1 60
    coordinateU := generatorCoordinates81 0
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 1 61
    coordinateU := generatorCoordinates81 7
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 1 62
    coordinateU := generatorCoordinates81 7
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 1 63
    coordinateU := generatorCoordinates81 6
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks1_valid : ∀ i, (generatorLeafBlocks1 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks1 i).coordinateU.IsValid ∧
      (generatorLeafBlocks1 i).coordinateV.IsValid ∧
      (generatorLeafBlocks1 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates84_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates85_valid 4,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 11⟩
    · exact ⟨generatorCoordinates86_valid 6,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 10⟩
    · exact ⟨generatorCoordinates86_valid 6,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates86_valid 5,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates86_valid 5,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 8⟩
    · exact ⟨generatorCoordinates85_valid 3,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates86_valid 4,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 8⟩
    · exact ⟨generatorCoordinates86_valid 4,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 7⟩
    · exact ⟨generatorCoordinates86_valid 3,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 7⟩
    · exact ⟨generatorCoordinates86_valid 3,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 6⟩
    · exact ⟨generatorCoordinates84_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates85_valid 2,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 7⟩
    · exact ⟨generatorCoordinates86_valid 2,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 6⟩
    · exact ⟨generatorCoordinates86_valid 2,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates86_valid 1,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates86_valid 1,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 4⟩
    · exact ⟨generatorCoordinates85_valid 1,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates85_valid 1,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 5 3⟩
    · exact ⟨generatorCoordinates83_valid 4,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates83_valid 4,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates84_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 5 17⟩
    · exact ⟨generatorCoordinates84_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates83_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates83_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates84_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates84_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates83_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates83_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates83_valid 4,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates84_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates85_valid 0,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 3⟩
    · exact ⟨generatorCoordinates85_valid 0,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates84_valid 7,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates84_valid 7,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 5 1⟩
    · exact ⟨generatorCoordinates84_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates84_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates83_valid 3,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates83_valid 3,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates80_valid 5,
        generatorCoordinates21_valid 4, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates80_valid 4,
        generatorCoordinates21_valid 5, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates80_valid 4,
        generatorCoordinates21_valid 4, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates80_valid 3,
        generatorCoordinates18_valid 0, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates80_valid 5,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates80_valid 5,
        generatorCoordinates13_valid 6, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates80_valid 4,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates80_valid 4,
        generatorCoordinates13_valid 6, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates80_valid 5,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates80_valid 5,
        generatorCoordinates9_valid 3, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates80_valid 4,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates80_valid 7,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates80_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates80_valid 6,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates80_valid 6,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates80_valid 5,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates81_valid 1,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates82_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 5 17⟩
    · exact ⟨generatorCoordinates82_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates82_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates82_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates81_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates81_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates81_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates81_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 5 9⟩
  have hMeta : ∀ i, (generatorLeafBlocks1 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks1 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
