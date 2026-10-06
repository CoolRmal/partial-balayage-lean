/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates24
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates27
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates28

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 82 of the recorded finite partition. -/
def generatorLeafBlocks82 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 82 0
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates22 5
    terms := 2
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 82 1
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates22 4
    terms := 2
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 82 2
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 82 3
    coordinateU := generatorCoordinates28 6
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 28
  },
  {
    rectangle := generatorPartitionRectangles 82 4
    coordinateU := generatorCoordinates28 6
    coordinateV := generatorCoordinates23 2
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 82 5
    coordinateU := generatorCoordinates28 5
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 82 6
    coordinateU := generatorCoordinates28 5
    coordinateV := generatorCoordinates23 2
    terms := 3
    radialRoot := generatorRadialRoots 2 26
  },
  {
    rectangle := generatorPartitionRectangles 82 7
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 82 8
    coordinateU := generatorCoordinates28 4
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 26
  },
  {
    rectangle := generatorPartitionRectangles 82 9
    coordinateU := generatorCoordinates28 4
    coordinateV := generatorCoordinates23 2
    terms := 4
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 82 10
    coordinateU := generatorCoordinates28 3
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 82 11
    coordinateU := generatorCoordinates28 3
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 24
  },
  {
    rectangle := generatorPartitionRectangles 82 12
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates21 7
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 82 13
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 82 14
    coordinateU := generatorCoordinates28 2
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 24
  },
  {
    rectangle := generatorPartitionRectangles 82 15
    coordinateU := generatorCoordinates28 2
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 16
    coordinateU := generatorCoordinates28 1
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 17
    coordinateU := generatorCoordinates28 1
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 22
  },
  {
    rectangle := generatorPartitionRectangles 82 18
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 19
    coordinateU := generatorCoordinates28 0
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 22
  },
  {
    rectangle := generatorPartitionRectangles 82 20
    coordinateU := generatorCoordinates28 0
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 82 21
    coordinateU := generatorCoordinates27 7
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 82 22
    coordinateU := generatorCoordinates27 7
    coordinateV := generatorCoordinates23 2
    terms := 4
    radialRoot := generatorRadialRoots 2 20
  },
  {
    rectangle := generatorPartitionRectangles 82 23
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates24 7
    terms := 4
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 82 24
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates24 6
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 82 25
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates24 7
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 82 26
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates24 6
    terms := 3
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 82 27
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates23 0
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 82 28
    coordinateU := generatorCoordinates27 4
    coordinateV := generatorCoordinates24 7
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 82 29
    coordinateU := generatorCoordinates27 4
    coordinateV := generatorCoordinates24 6
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 82 30
    coordinateU := generatorCoordinates27 3
    coordinateV := generatorCoordinates24 7
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 82 31
    coordinateU := generatorCoordinates27 3
    coordinateV := generatorCoordinates24 6
    terms := 3
    radialRoot := generatorRadialRoots 2 30
  },
  {
    rectangle := generatorPartitionRectangles 82 32
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates23 0
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 82 33
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates22 0
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 82 34
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates23 1
    terms := 5
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 82 35
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates23 0
    terms := 2
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 82 36
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates23 1
    terms := 4
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 82 37
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates23 0
    terms := 2
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 82 38
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates22 7
    terms := 2
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 82 39
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates22 6
    terms := 1
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 40
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates22 7
    terms := 1
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 41
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates22 6
    terms := 1
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 82 42
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates21 7
    terms := 2
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 43
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates22 3
    terms := 2
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 82 44
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates23 3
    terms := 2
    radialRoot := generatorRadialRoots 2 20
  },
  {
    rectangle := generatorPartitionRectangles 82 45
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates23 2
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 82 46
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates23 3
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 82 47
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates23 2
    terms := 2
    radialRoot := generatorRadialRoots 2 18
  },
  {
    rectangle := generatorPartitionRectangles 82 48
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates22 3
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 82 49
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates22 2
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 82 50
    coordinateU := generatorCoordinates25 3
    coordinateV := generatorCoordinates21 7
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 82 51
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates22 3
    terms := 1
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 82 52
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates22 2
    terms := 1
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 82 53
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates22 3
    terms := 1
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 82 54
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates22 2
    terms := 1
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 82 55
    coordinateU := generatorCoordinates28 6
    coordinateV := generatorCoordinates21 0
    terms := 3
    radialRoot := generatorRadialRoots 2 26
  },
  {
    rectangle := generatorPartitionRectangles 82 56
    coordinateU := generatorCoordinates28 6
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 82 57
    coordinateU := generatorCoordinates28 5
    coordinateV := generatorCoordinates21 0
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 82 58
    coordinateU := generatorCoordinates28 5
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 24
  },
  {
    rectangle := generatorPartitionRectangles 82 59
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 60
    coordinateU := generatorCoordinates28 4
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 24
  },
  {
    rectangle := generatorPartitionRectangles 82 61
    coordinateU := generatorCoordinates28 4
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 62
    coordinateU := generatorCoordinates28 3
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 82 63
    coordinateU := generatorCoordinates28 3
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 22
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks82_valid : ∀ i, (generatorLeafBlocks82 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks82 i).coordinateU.IsValid ∧
      (generatorLeafBlocks82 i).coordinateV.IsValid ∧
      (generatorLeafBlocks82 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates28_valid 6,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 28⟩
    · exact ⟨generatorCoordinates28_valid 6,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates28_valid 5,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates28_valid 5,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 26⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates28_valid 4,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 26⟩
    · exact ⟨generatorCoordinates28_valid 4,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates28_valid 3,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates28_valid 3,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 24⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates28_valid 2,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 24⟩
    · exact ⟨generatorCoordinates28_valid 2,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates28_valid 1,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates28_valid 1,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 22⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates28_valid 0,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 22⟩
    · exact ⟨generatorCoordinates28_valid 0,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates27_valid 7,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates27_valid 7,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 20⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates24_valid 7, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates24_valid 6, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates24_valid 7, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates24_valid 6, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates27_valid 4,
        generatorCoordinates24_valid 7, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates27_valid 4,
        generatorCoordinates24_valid 6, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates27_valid 3,
        generatorCoordinates24_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates27_valid 3,
        generatorCoordinates24_valid 6, generatorRadialRoots_valid 2 30⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 20⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 18⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates25_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates28_valid 6,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 26⟩
    · exact ⟨generatorCoordinates28_valid 6,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates28_valid 5,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates28_valid 5,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 24⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates28_valid 4,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 24⟩
    · exact ⟨generatorCoordinates28_valid 4,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates28_valid 3,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates28_valid 3,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 22⟩
  have hMeta : ∀ i, (generatorLeafBlocks82 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks82 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
