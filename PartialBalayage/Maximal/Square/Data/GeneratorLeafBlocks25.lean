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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates58
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates60
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates62

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 25 of the recorded finite partition. -/
def generatorLeafBlocks25 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 25 0
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 25 1
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 25 2
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates0 3
    terms := 5
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 25 3
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 25 4
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates0 3
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 25 5
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates55 2
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 25 6
    coordinateU := generatorCoordinates59 4
    coordinateV := generatorCoordinates55 3
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 25 7
    coordinateU := generatorCoordinates59 4
    coordinateV := generatorCoordinates55 2
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 25 8
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates50 7
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 25 9
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates50 6
    terms := 0
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 25 10
    coordinateU := generatorCoordinates59 4
    coordinateV := generatorCoordinates50 7
    terms := 1
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 25 11
    coordinateU := generatorCoordinates59 4
    coordinateV := generatorCoordinates50 6
    terms := 8
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 25 12
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates46 3
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 25 13
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates46 2
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 25 14
    coordinateU := generatorCoordinates59 4
    coordinateV := generatorCoordinates46 3
    terms := 8
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 25 15
    coordinateU := generatorCoordinates59 4
    coordinateV := generatorCoordinates46 2
    terms := 2
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 25 16
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates41 4
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 25 17
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates41 3
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 25 18
    coordinateU := generatorCoordinates59 4
    coordinateV := generatorCoordinates41 4
    terms := 4
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 25 19
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates41 6
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 25 20
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates41 5
    terms := 1
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 25 21
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates41 6
    terms := 2
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 25 22
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates41 5
    terms := 8
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 25 23
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates37 3
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 25 24
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates37 2
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 25 25
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates37 3
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 25 26
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates37 2
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 25 27
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates37 1
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 25 28
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates37 0
    terms := 12
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 25 29
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates37 1
    terms := 3
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 25 30
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates37 5
    terms := 3
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 25 31
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates37 4
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 25 32
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates37 5
    terms := 4
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 25 33
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates37 4
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 25 34
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates37 3
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 25 35
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates37 2
    terms := 3
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 25 36
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates38 3
    terms := 2
    radialRoot := generatorRadialRoots 5 17
  },
  {
    rectangle := generatorPartitionRectangles 25 37
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates38 2
    terms := 3
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 25 38
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates38 3
    terms := 5
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 25 39
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates38 2
    terms := 8
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 25 40
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates38 1
    terms := 3
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 25 41
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates38 0
    terms := 4
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 25 42
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates38 1
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 25 43
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates38 0
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 25 44
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates37 1
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 25 45
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates37 5
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 25 46
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates37 4
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 25 47
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates37 5
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 25 48
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates37 4
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 25 49
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates37 7
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 25 50
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates37 6
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 25 51
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates37 7
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 25 52
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates37 6
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 25 53
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates37 5
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 25 54
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates37 4
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 25 55
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates37 5
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 25 56
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates37 4
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 25 57
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates34 4
    terms := 4
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 25 58
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates34 3
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 25 59
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates34 4
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 25 60
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 25 61
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates34 2
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 25 62
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates34 1
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 25 63
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates34 2
    terms := 20
    radialRoot := generatorRadialRoots 5 2
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks25_valid : ∀ i, (generatorLeafBlocks25 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks25 i).coordinateU.IsValid ∧
      (generatorLeafBlocks25 i).coordinateV.IsValid ∧
      (generatorLeafBlocks25 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates55_valid 2, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates59_valid 4,
        generatorCoordinates55_valid 3, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates59_valid 4,
        generatorCoordinates55_valid 2, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates50_valid 7, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates50_valid 6, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates59_valid 4,
        generatorCoordinates50_valid 7, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates59_valid 4,
        generatorCoordinates50_valid 6, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates46_valid 3, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates46_valid 2, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates59_valid 4,
        generatorCoordinates46_valid 3, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates59_valid 4,
        generatorCoordinates46_valid 2, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates41_valid 4, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates41_valid 3, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates59_valid 4,
        generatorCoordinates41_valid 4, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 5 17⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 5 2⟩
  have hMeta : ∀ i, (generatorLeafBlocks25 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks25 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
