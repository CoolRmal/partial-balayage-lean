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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 78 of the recorded finite partition. -/
def generatorLeafBlocks78 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 78 0
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 78 1
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 2
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 3
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 78 4
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates14 7
    terms := 2
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 78 5
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates14 6
    terms := 2
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 6
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates14 7
    terms := 2
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 7
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates14 6
    terms := 2
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 78 8
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates14 5
    terms := 2
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 78 9
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 78 10
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates14 5
    terms := 2
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 78 11
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 78 12
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 78 13
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 78 14
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 78 15
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 78 16
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates10 6
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 78 17
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates10 5
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 18
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates10 6
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 19
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates10 5
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 78 20
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 78 21
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 22
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 78 23
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 78 24
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates9 7
    terms := 4
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 78 25
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 78 26
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 78 27
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 78 28
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 78 29
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 78 30
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 78 31
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 78 32
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 78 33
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates9 6
    terms := 5
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 78 34
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 78 35
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 78 36
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 78 37
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 78 38
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 78 39
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 78 40
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 78 41
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 78 42
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 78 43
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 78 44
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 78 45
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 78 46
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 78 47
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates10 6
    terms := 2
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 78 48
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates10 5
    terms := 2
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 78 49
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates10 6
    terms := 2
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 78 50
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates10 5
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 78 51
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 78 52
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 78 53
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 78 54
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 78 55
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 78 56
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 78 57
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 78 58
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 78 59
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates10 4
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 78 60
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 78 61
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates10 4
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 78 62
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 78 63
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks78_valid : ∀ i, (generatorLeafBlocks78 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks78 i).coordinateU.IsValid ∧
      (generatorLeafBlocks78 i).coordinateV.IsValid ∧
      (generatorLeafBlocks78 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 61⟩
  have hMeta : ∀ i, (generatorLeafBlocks78 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks78 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
