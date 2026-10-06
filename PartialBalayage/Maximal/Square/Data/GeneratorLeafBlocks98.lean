/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates7
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates8
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates16
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates17

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 98 of the recorded finite partition. -/
def generatorLeafBlocks98 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 98 0
    coordinateU := generatorCoordinates14 3
    coordinateV := generatorCoordinates9 6
    terms := 0
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 98 1
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates10 2
    terms := 0
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 98 2
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates10 1
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 98 3
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates10 2
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 98 4
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates10 1
    terms := 0
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 98 5
    coordinateU := generatorCoordinates14 2
    coordinateV := generatorCoordinates9 6
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 98 6
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates10 2
    terms := 0
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 98 7
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates10 1
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 98 8
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates10 2
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 98 9
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates10 1
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 98 10
    coordinateU := generatorCoordinates13 6
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 98 11
    coordinateU := generatorCoordinates14 1
    coordinateV := generatorCoordinates9 6
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 98 12
    coordinateU := generatorCoordinates14 1
    coordinateV := generatorCoordinates9 5
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 13
    coordinateU := generatorCoordinates14 0
    coordinateV := generatorCoordinates9 6
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 14
    coordinateU := generatorCoordinates14 0
    coordinateV := generatorCoordinates9 5
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 98 15
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 98 16
    coordinateU := generatorCoordinates15 3
    coordinateV := generatorCoordinates6 4
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 98 17
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 98 18
    coordinateU := generatorCoordinates15 2
    coordinateV := generatorCoordinates6 4
    terms := 1
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 98 19
    coordinateU := generatorCoordinates17 3
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 10
  },
  {
    rectangle := generatorPartitionRectangles 98 20
    coordinateU := generatorCoordinates17 3
    coordinateV := generatorCoordinates7 2
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 98 21
    coordinateU := generatorCoordinates17 2
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 98 22
    coordinateU := generatorCoordinates17 2
    coordinateV := generatorCoordinates7 2
    terms := 0
    radialRoot := generatorRadialRoots 1 8
  },
  {
    rectangle := generatorPartitionRectangles 98 23
    coordinateU := generatorCoordinates17 3
    coordinateV := generatorCoordinates7 1
    terms := 0
    radialRoot := generatorRadialRoots 1 8
  },
  {
    rectangle := generatorPartitionRectangles 98 24
    coordinateU := generatorCoordinates17 3
    coordinateV := generatorCoordinates7 0
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 25
    coordinateU := generatorCoordinates17 2
    coordinateV := generatorCoordinates7 1
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 26
    coordinateU := generatorCoordinates17 2
    coordinateV := generatorCoordinates7 0
    terms := 1
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 98 27
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 8
  },
  {
    rectangle := generatorPartitionRectangles 98 28
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates7 2
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 29
    coordinateU := generatorCoordinates17 0
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 30
    coordinateU := generatorCoordinates17 0
    coordinateV := generatorCoordinates7 2
    terms := 1
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 98 31
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates7 1
    terms := 1
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 98 32
    coordinateU := generatorCoordinates17 1
    coordinateV := generatorCoordinates7 0
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 98 33
    coordinateU := generatorCoordinates17 7
    coordinateV := generatorCoordinates8 3
    terms := 1
    radialRoot := generatorRadialRoots 1 5
  },
  {
    rectangle := generatorPartitionRectangles 98 34
    coordinateU := generatorCoordinates17 7
    coordinateV := generatorCoordinates8 2
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 98 35
    coordinateU := generatorCoordinates17 6
    coordinateV := generatorCoordinates8 3
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 98 36
    coordinateU := generatorCoordinates17 6
    coordinateV := generatorCoordinates8 2
    terms := 1
    radialRoot := generatorRadialRoots 1 3
  },
  {
    rectangle := generatorPartitionRectangles 98 37
    coordinateU := generatorCoordinates17 7
    coordinateV := generatorCoordinates8 1
    terms := 1
    radialRoot := generatorRadialRoots 1 3
  },
  {
    rectangle := generatorPartitionRectangles 98 38
    coordinateU := generatorCoordinates17 7
    coordinateV := generatorCoordinates8 0
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 98 39
    coordinateU := generatorCoordinates17 6
    coordinateV := generatorCoordinates8 1
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 98 40
    coordinateU := generatorCoordinates17 6
    coordinateV := generatorCoordinates8 0
    terms := 1
    radialRoot := generatorRadialRoots 1 1
  },
  {
    rectangle := generatorPartitionRectangles 98 41
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 98 42
    coordinateU := generatorCoordinates15 1
    coordinateV := generatorCoordinates6 4
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 43
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 98 44
    coordinateU := generatorCoordinates15 0
    coordinateV := generatorCoordinates6 4
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 98 45
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 98 46
    coordinateU := generatorCoordinates16 7
    coordinateV := generatorCoordinates7 2
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 98 47
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 98 48
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates7 2
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 98 49
    coordinateU := generatorCoordinates17 5
    coordinateV := generatorCoordinates8 3
    terms := 1
    radialRoot := generatorRadialRoots 1 3
  },
  {
    rectangle := generatorPartitionRectangles 98 50
    coordinateU := generatorCoordinates17 5
    coordinateV := generatorCoordinates8 2
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 98 51
    coordinateU := generatorCoordinates17 4
    coordinateV := generatorCoordinates8 3
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 98 52
    coordinateU := generatorCoordinates17 4
    coordinateV := generatorCoordinates8 2
    terms := 1
    radialRoot := generatorRadialRoots 1 1
  },
  {
    rectangle := generatorPartitionRectangles 98 53
    coordinateU := generatorCoordinates17 5
    coordinateV := generatorCoordinates8 1
    terms := 1
    radialRoot := generatorRadialRoots 1 1
  },
  {
    rectangle := generatorPartitionRectangles 98 54
    coordinateU := generatorCoordinates17 5
    coordinateV := generatorCoordinates8 0
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 98 55
    coordinateU := generatorCoordinates17 4
    coordinateV := generatorCoordinates8 1
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 98 56
    coordinateU := generatorCoordinates17 4
    coordinateV := generatorCoordinates8 0
    terms := 1
    radialRoot := generatorRadialRoots 0 63
  },
  {
    rectangle := generatorPartitionRectangles 98 57
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates7 1
    terms := 2
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 98 58
    coordinateU := generatorCoordinates16 6
    coordinateV := generatorCoordinates7 0
    terms := 2
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 98 59
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 98 60
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates7 2
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 98 61
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates7 3
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 98 62
    coordinateU := generatorCoordinates16 4
    coordinateV := generatorCoordinates7 2
    terms := 0
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 98 63
    coordinateU := generatorCoordinates16 5
    coordinateV := generatorCoordinates7 1
    terms := 1
    radialRoot := generatorRadialRoots 0 62
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks98_valid : ∀ i, (generatorLeafBlocks98 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks98 i).coordinateU.IsValid ∧
      (generatorLeafBlocks98 i).coordinateV.IsValid ∧
      (generatorLeafBlocks98 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates14_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates14_valid 2,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates13_valid 6,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates14_valid 1,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates14_valid 1,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates14_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates14_valid 0,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates15_valid 3,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates15_valid 2,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates17_valid 3,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 10⟩
    · exact ⟨generatorCoordinates17_valid 3,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates17_valid 2,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates17_valid 2,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 1 8⟩
    · exact ⟨generatorCoordinates17_valid 3,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 1 8⟩
    · exact ⟨generatorCoordinates17_valid 3,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates17_valid 2,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates17_valid 2,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 8⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates17_valid 0,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates17_valid 0,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates17_valid 1,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates17_valid 7,
        generatorCoordinates8_valid 3, generatorRadialRoots_valid 1 5⟩
    · exact ⟨generatorCoordinates17_valid 7,
        generatorCoordinates8_valid 2, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates17_valid 6,
        generatorCoordinates8_valid 3, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates17_valid 6,
        generatorCoordinates8_valid 2, generatorRadialRoots_valid 1 3⟩
    · exact ⟨generatorCoordinates17_valid 7,
        generatorCoordinates8_valid 1, generatorRadialRoots_valid 1 3⟩
    · exact ⟨generatorCoordinates17_valid 7,
        generatorCoordinates8_valid 0, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates17_valid 6,
        generatorCoordinates8_valid 1, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates17_valid 6,
        generatorCoordinates8_valid 0, generatorRadialRoots_valid 1 1⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates15_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates15_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates16_valid 7,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates17_valid 5,
        generatorCoordinates8_valid 3, generatorRadialRoots_valid 1 3⟩
    · exact ⟨generatorCoordinates17_valid 5,
        generatorCoordinates8_valid 2, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates17_valid 4,
        generatorCoordinates8_valid 3, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates17_valid 4,
        generatorCoordinates8_valid 2, generatorRadialRoots_valid 1 1⟩
    · exact ⟨generatorCoordinates17_valid 5,
        generatorCoordinates8_valid 1, generatorRadialRoots_valid 1 1⟩
    · exact ⟨generatorCoordinates17_valid 5,
        generatorCoordinates8_valid 0, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates17_valid 4,
        generatorCoordinates8_valid 1, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates17_valid 4,
        generatorCoordinates8_valid 0, generatorRadialRoots_valid 0 63⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates16_valid 6,
        generatorCoordinates7_valid 0, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates7_valid 3, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates16_valid 4,
        generatorCoordinates7_valid 2, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates16_valid 5,
        generatorCoordinates7_valid 1, generatorRadialRoots_valid 0 62⟩
  have hMeta : ∀ i, (generatorLeafBlocks98 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks98 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
