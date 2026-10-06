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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates58
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates60

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 29 of the recorded finite partition. -/
def generatorLeafBlocks29 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 29 0
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 29 1
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 29 2
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 29 3
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 29 4
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 29 5
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 29 6
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 29 7
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 29 8
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 29 9
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 29 10
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 29 11
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 29 12
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 29 13
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 29 14
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 29 15
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 29 16
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 29 17
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 29 18
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 29 19
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 29 20
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 29 21
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 29 22
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 29 23
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 29 24
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates5 7
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 29 25
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates5 6
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 29 26
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 29 27
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 29 28
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 29 29
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 29 30
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 29 31
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 29 32
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 29 33
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 29 34
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 29 35
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 29 36
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 29 37
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 29 38
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 29 39
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates0 3
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 29 40
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 29 41
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates0 3
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 29 42
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 29 43
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 29 44
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 29 45
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 29 46
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 29 47
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 29 48
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 29 49
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates1 6
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 29 50
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates1 5
    terms := 8
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 29 51
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 29 52
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 29 53
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 29 54
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 29 55
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 29 56
    coordinateU := generatorCoordinates55 3
    coordinateV := generatorCoordinates55 3
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 29 57
    coordinateU := generatorCoordinates55 3
    coordinateV := generatorCoordinates55 2
    terms := 0
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 29 58
    coordinateU := generatorCoordinates55 2
    coordinateV := generatorCoordinates55 3
    terms := 0
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 29 59
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates55 5
    terms := 0
    radialRoot := generatorRadialRoots 5 45
  },
  {
    rectangle := generatorPartitionRectangles 29 60
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates55 4
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 29 61
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates55 5
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 29 62
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates55 4
    terms := 2
    radialRoot := generatorRadialRoots 5 43
  },
  {
    rectangle := generatorPartitionRectangles 29 63
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates51 3
    terms := 0
    radialRoot := generatorRadialRoots 5 45
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks29_valid : ∀ i, (generatorLeafBlocks29 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks29 i).coordinateU.IsValid ∧
      (generatorLeafBlocks29 i).coordinateV.IsValid ∧
      (generatorLeafBlocks29 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates55_valid 3,
        generatorCoordinates55_valid 3, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates55_valid 3,
        generatorCoordinates55_valid 2, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates55_valid 2,
        generatorCoordinates55_valid 3, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates55_valid 5, generatorRadialRoots_valid 5 45⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates55_valid 4, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates55_valid 5, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates55_valid 4, generatorRadialRoots_valid 5 43⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates51_valid 3, generatorRadialRoots_valid 5 45⟩
  have hMeta : ∀ i, (generatorLeafBlocks29 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks29 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
