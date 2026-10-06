/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
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

/-- Actual source leaf candidates, block 23 of the recorded finite partition. -/
def generatorLeafBlocks23 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 23 0
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 23 1
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 23 2
    coordinateU := generatorCoordinates63 6
    coordinateV := generatorCoordinates23 0
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 23 3
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 23 4
    coordinateU := generatorCoordinates63 5
    coordinateV := generatorCoordinates23 0
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 23 5
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates22 0
    terms := 30
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 23 6
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 23 7
    coordinateU := generatorCoordinates63 4
    coordinateV := generatorCoordinates23 0
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 23 8
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates23 1
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 23 9
    coordinateU := generatorCoordinates63 3
    coordinateV := generatorCoordinates23 0
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 23 10
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates22 0
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 23 11
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates21 7
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 23 12
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates21 6
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 23 13
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates21 7
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 23 14
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates21 6
    terms := 30
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 23 15
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates22 1
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 23 16
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates22 0
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 23 17
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates22 1
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 23 18
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates22 0
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 23 19
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates21 7
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 23 20
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates22 3
    terms := 20
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 23 21
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates22 2
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 23 22
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 23 23
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates22 2
    terms := 20
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 23 24
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates21 7
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 23 25
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 23 26
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates22 2
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 23 27
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 23 28
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates22 2
    terms := 20
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 23 29
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates18 6
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 23 30
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 23 31
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates18 6
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 23 32
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 23 33
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 23 34
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates18 3
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 23 35
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 23 36
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates18 3
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 23 37
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates19 6
    terms := 20
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 23 38
    coordinateU := generatorCoordinates63 2
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 23 39
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates19 6
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 23 40
    coordinateU := generatorCoordinates63 1
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 23 41
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 23 42
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates19 6
    terms := 20
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 23 43
    coordinateU := generatorCoordinates63 0
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 23 44
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates19 6
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 23 45
    coordinateU := generatorCoordinates62 7
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 23 46
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 23 47
    coordinateU := generatorCoordinates62 1
    coordinateV := generatorCoordinates18 1
    terms := 20
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 23 48
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 23 49
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 23 50
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 23 51
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 23 52
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 23 53
    coordinateU := generatorCoordinates62 6
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 23 54
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 23 55
    coordinateU := generatorCoordinates62 5
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 23 56
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 23 57
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 23 58
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 23 59
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 23 60
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 23 61
    coordinateU := generatorCoordinates62 4
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 23 62
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 23 63
    coordinateU := generatorCoordinates62 3
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks23_valid : ∀ i, (generatorLeafBlocks23 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks23 i).coordinateU.IsValid ∧
      (generatorLeafBlocks23 i).coordinateV.IsValid ∧
      (generatorLeafBlocks23 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates63_valid 6,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates63_valid 5,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates63_valid 4,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates63_valid 3,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates63_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates63_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates63_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates62_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates62_valid 1,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates62_valid 6,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates62_valid 5,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates62_valid 4,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates62_valid 3,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 35⟩
  have hMeta : ∀ i, (generatorLeafBlocks23 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks23 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
