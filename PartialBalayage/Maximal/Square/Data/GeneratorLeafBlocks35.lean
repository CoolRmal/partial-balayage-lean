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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates56

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 35 of the recorded finite partition. -/
def generatorLeafBlocks35 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 35 0
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 35 1
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 35 2
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 35 3
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates23 0
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 35 4
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 35 5
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates23 0
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 35 6
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 35 7
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 35 8
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 35 9
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 35 10
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 35 11
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 35 12
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 35 13
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 35 14
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 35 15
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 35 16
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 35 17
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 35 18
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 35 19
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 35 20
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 35 21
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 35 22
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 35 23
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 35 24
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 35 25
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 35 26
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 35 27
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 35 28
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 35 29
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 35 30
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 35 31
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 35 32
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 35 33
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 35 34
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 35 35
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 35 36
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 35 37
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 35 38
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 35 39
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 35 40
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 35 41
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 35 42
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 35 43
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 35 44
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 35 45
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 35 46
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 35 47
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 35 48
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 35 49
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 35 50
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 35 51
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 35 52
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 35 53
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 35 54
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 35 55
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 35 56
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 35 57
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 35 58
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 35 59
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 35 60
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 35 61
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 35 62
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 35 63
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks35_valid : ∀ i, (generatorLeafBlocks35 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks35 i).coordinateU.IsValid ∧
      (generatorLeafBlocks35 i).coordinateV.IsValid ∧
      (generatorLeafBlocks35 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 18⟩
  have hMeta : ∀ i, (generatorLeafBlocks35 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks35 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
