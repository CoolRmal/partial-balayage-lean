/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
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

/-- Actual source leaf candidates, block 28 of the recorded finite partition. -/
def generatorLeafBlocks28 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 28 0
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 28 1
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 28 2
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 28 3
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 28 4
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 28 5
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 28 6
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 28 7
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 28 8
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 28 9
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 28 10
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 28 11
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 28 12
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 28 13
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 28 14
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 28 15
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 28 16
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 28 17
    coordinateU := generatorCoordinates59 5
    coordinateV := generatorCoordinates18 1
    terms := 20
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 28 18
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 28 19
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 28 20
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 28 21
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 28 22
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 28 23
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 28 24
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 28 25
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 28 26
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 28 27
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 28 28
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 28 29
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates18 3
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 28 30
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 28 31
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates18 3
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 28 32
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 28 33
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 28 34
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 28 35
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 28 36
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 28 37
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 28 38
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 28 39
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 28 40
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 28 41
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 28 42
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 28 43
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 28 44
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 28 45
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 28 46
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 28 47
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 28 48
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 28 49
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 28 50
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 28 51
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 28 52
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 28 53
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 28 54
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 28 55
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 28 56
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 28 57
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 28 58
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 28 59
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 28 60
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 28 61
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 28 62
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 28 63
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks28_valid : ∀ i, (generatorLeafBlocks28 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks28 i).coordinateU.IsValid ∧
      (generatorLeafBlocks28 i).coordinateV.IsValid ∧
      (generatorLeafBlocks28 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates59_valid 5,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 14⟩
  have hMeta : ∀ i, (generatorLeafBlocks28 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks28 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
