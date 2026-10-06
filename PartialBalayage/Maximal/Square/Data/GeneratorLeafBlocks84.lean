/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 84 of the recorded finite partition. -/
def generatorLeafBlocks84 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 84 0
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 84 1
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 84 2
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 84 3
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 84 4
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 84 5
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 84 6
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 84 7
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 84 8
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 84 9
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates15 0
    terms := 4
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 84 10
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 84 11
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 84 12
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 84 13
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 84 14
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates14 5
    terms := 2
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 84 15
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 16
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates14 5
    terms := 2
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 17
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 18
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 84 19
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 20
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 21
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 22
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 23
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 24
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 25
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 84 26
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 84 27
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 84 28
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates15 3
    terms := 1
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 84 29
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates15 2
    terms := 1
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 84 30
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates15 1
    terms := 2
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 84 31
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 32
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates15 1
    terms := 2
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 33
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates15 0
    terms := 2
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 34
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates15 3
    terms := 1
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 84 35
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates15 2
    terms := 1
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 36
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates15 3
    terms := 1
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 84 37
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates15 2
    terms := 1
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 38
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates15 1
    terms := 1
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 39
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates15 0
    terms := 1
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 40
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates15 1
    terms := 1
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 41
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates15 0
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 84 42
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 43
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 44
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates14 7
    terms := 2
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 45
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates14 6
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 84 46
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates14 5
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 84 47
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 84 48
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates14 5
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 84 49
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates14 4
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 84 50
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates14 7
    terms := 1
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 84 51
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates14 6
    terms := 1
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 84 52
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates14 7
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 84 53
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates14 6
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 84 54
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates14 5
    terms := 1
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 84 55
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates14 4
    terms := 1
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 84 56
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates14 5
    terms := 1
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 84 57
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates14 4
    terms := 1
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 84 58
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 84 59
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 60
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 84 61
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 84 62
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates10 6
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 84 63
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates10 5
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks84_valid : ∀ i, (generatorLeafBlocks84 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks84 i).coordinateU.IsValid ∧
      (generatorLeafBlocks84 i).coordinateV.IsValid ∧
      (generatorLeafBlocks84 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 63⟩
  have hMeta : ∀ i, (generatorLeafBlocks84 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks84 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
