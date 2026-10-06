/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
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

/-- Actual source leaf candidates, block 34 of the recorded finite partition. -/
def generatorLeafBlocks34 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 34 0
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates29 3
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 34 1
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 34 2
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates29 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 34 3
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates29 4
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 34 4
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates30 5
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 34 5
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates30 4
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 34 6
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates30 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 34 7
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates30 4
    terms := 20
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 34 8
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates30 3
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 34 9
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates30 2
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 34 10
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates30 3
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 34 11
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates30 2
    terms := 20
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 34 12
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates29 3
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 34 13
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 34 14
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 34 15
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 34 16
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates30 1
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 34 17
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 34 18
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 34 19
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 34 20
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 34 21
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates29 6
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 34 22
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 34 23
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 34 24
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 34 25
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 34 26
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 34 27
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 34 28
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 34 29
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 34 30
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 34 31
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates25 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 34 32
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 34 33
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 34 34
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 34 35
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 34 36
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 34 37
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 34 38
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 34 39
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 34 40
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 34 41
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 34 42
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 34 43
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 34 44
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 34 45
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 34 46
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 34 47
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 34 48
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 34 49
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 34 50
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates22 1
    terms := 20
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 34 51
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 34 52
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates22 1
    terms := 20
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 34 53
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 34 54
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 34 55
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 34 56
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 34 57
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 34 58
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 34 59
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 34 60
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 34 61
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 34 62
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 34 63
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks34_valid : ∀ i, (generatorLeafBlocks34 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks34 i).coordinateU.IsValid ∧
      (generatorLeafBlocks34 i).coordinateV.IsValid ∧
      (generatorLeafBlocks34 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates30_valid 4, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 40⟩
  have hMeta : ∀ i, (generatorLeafBlocks34 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks34 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
