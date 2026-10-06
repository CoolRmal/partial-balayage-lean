/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates16
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates24

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 88 of the recorded finite partition. -/
def generatorLeafBlocks88 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 88 0
    coordinateU := generatorCoordinates21 7
    coordinateV := generatorCoordinates21 7
    terms := 0
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 88 1
    coordinateU := generatorCoordinates21 7
    coordinateV := generatorCoordinates21 6
    terms := 0
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 88 2
    coordinateU := generatorCoordinates21 6
    coordinateV := generatorCoordinates21 7
    terms := 0
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 88 3
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates22 3
    terms := 0
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 88 4
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates22 2
    terms := 0
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 88 5
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates22 3
    terms := 0
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 88 6
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates22 2
    terms := 0
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 88 7
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates19 6
    terms := 1
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 88 8
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates19 5
    terms := 1
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 88 9
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates19 6
    terms := 0
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 88 10
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates19 5
    terms := 0
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 88 11
    coordinateU := generatorCoordinates22 1
    coordinateV := generatorCoordinates18 5
    terms := 4
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 88 12
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates18 6
    terms := 1
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 88 13
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates18 5
    terms := 1
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 88 14
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates19 2
    terms := 1
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 88 15
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates19 1
    terms := 1
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 88 16
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates19 2
    terms := 1
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 88 17
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates19 1
    terms := 1
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 88 18
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates19 0
    terms := 1
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 88 19
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates18 7
    terms := 1
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 88 20
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates19 0
    terms := 1
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 88 21
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates18 7
    terms := 1
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 88 22
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates18 4
    terms := 1
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 88 23
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates19 0
    terms := 1
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 88 24
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates18 7
    terms := 1
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 88 25
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates19 0
    terms := 0
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 88 26
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates18 7
    terms := 1
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 88 27
    coordinateU := generatorCoordinates21 7
    coordinateV := generatorCoordinates18 6
    terms := 1
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 88 28
    coordinateU := generatorCoordinates21 7
    coordinateV := generatorCoordinates18 5
    terms := 0
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 88 29
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates19 6
    terms := 0
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 88 30
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates19 5
    terms := 0
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 88 31
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates19 6
    terms := 0
    radialRoot := generatorRadialRoots 2 5
  },
  {
    rectangle := generatorPartitionRectangles 88 32
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates19 5
    terms := 0
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 88 33
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates19 4
    terms := 0
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 88 34
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates19 3
    terms := 0
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 88 35
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates19 4
    terms := 0
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 88 36
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates19 3
    terms := 0
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 88 37
    coordinateU := generatorCoordinates21 7
    coordinateV := generatorCoordinates18 4
    terms := 0
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 88 38
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates19 0
    terms := 0
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 88 39
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates18 7
    terms := 0
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 88 40
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates19 0
    terms := 0
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 88 41
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates18 7
    terms := 0
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 88 42
    coordinateU := generatorCoordinates21 6
    coordinateV := generatorCoordinates18 4
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 88 43
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates19 0
    terms := 0
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 88 44
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates18 7
    terms := 0
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 88 45
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates19 0
    terms := 0
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 88 46
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates18 7
    terms := 0
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 88 47
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates15 3
    terms := 1
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 88 48
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 88 49
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates15 3
    terms := 1
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 88 50
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates15 2
    terms := 1
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 88 51
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 7
    terms := 1
    radialRoot := generatorRadialRoots 2 2
  },
  {
    rectangle := generatorPartitionRectangles 88 52
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 6
    terms := 1
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 88 53
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 7
    terms := 1
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 88 54
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 6
    terms := 1
    radialRoot := generatorRadialRoots 2 0
  },
  {
    rectangle := generatorPartitionRectangles 88 55
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 5
    terms := 1
    radialRoot := generatorRadialRoots 2 0
  },
  {
    rectangle := generatorPartitionRectangles 88 56
    coordinateU := generatorCoordinates24 7
    coordinateV := generatorCoordinates16 4
    terms := 1
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 88 57
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 5
    terms := 1
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 88 58
    coordinateU := generatorCoordinates24 6
    coordinateV := generatorCoordinates16 4
    terms := 1
    radialRoot := generatorRadialRoots 1 62
  },
  {
    rectangle := generatorPartitionRectangles 88 59
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 88 60
    coordinateU := generatorCoordinates24 5
    coordinateV := generatorCoordinates16 5
    terms := 2
    radialRoot := generatorRadialRoots 1 62
  },
  {
    rectangle := generatorPartitionRectangles 88 61
    coordinateU := generatorCoordinates24 5
    coordinateV := generatorCoordinates16 4
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 88 62
    coordinateU := generatorCoordinates24 4
    coordinateV := generatorCoordinates16 5
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 88 63
    coordinateU := generatorCoordinates24 4
    coordinateV := generatorCoordinates16 4
    terms := 2
    radialRoot := generatorRadialRoots 1 60
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks88_valid : ∀ i, (generatorLeafBlocks88 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks88 i).coordinateU.IsValid ∧
      (generatorLeafBlocks88 i).coordinateV.IsValid ∧
      (generatorLeafBlocks88 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates21_valid 7,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates21_valid 7,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates21_valid 6,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates22_valid 1,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates21_valid 7,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates21_valid 7,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 5⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates21_valid 7,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates21_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 7, generatorRadialRoots_valid 2 2⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 6, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 7, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 6, generatorRadialRoots_valid 2 0⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 2 0⟩
    · exact ⟨generatorCoordinates24_valid 7,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates24_valid 6,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 62⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates24_valid 5,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 1 62⟩
    · exact ⟨generatorCoordinates24_valid 5,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates24_valid 4,
        generatorCoordinates16_valid 5, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates24_valid 4,
        generatorCoordinates16_valid 4, generatorRadialRoots_valid 1 60⟩
  have hMeta : ∀ i, (generatorLeafBlocks88 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks88 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
