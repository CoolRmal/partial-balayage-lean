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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 65 of the recorded finite partition. -/
def generatorLeafBlocks65 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 65 0
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 65 1
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 65 2
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates21 7
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 65 3
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 65 4
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 65 5
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 65 6
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 65 7
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 65 8
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates22 0
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 65 9
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 65 10
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates23 0
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 65 11
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 65 12
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates23 0
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 65 13
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates22 0
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 65 14
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates21 7
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 65 15
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 65 16
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 65 17
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 65 18
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 65 19
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates21 7
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 65 20
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 65 21
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 65 22
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 65 23
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 60
  },
  {
    rectangle := generatorPartitionRectangles 65 24
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 65 25
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates23 3
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 65 26
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 58
  },
  {
    rectangle := generatorPartitionRectangles 65 27
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 65 28
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 65 29
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 65 30
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 65 31
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates18 5
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 65 32
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 65 33
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 65 34
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 65 35
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 65 36
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates18 5
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 65 37
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates18 4
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 65 38
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 65 39
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates18 4
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 65 40
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates18 3
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 65 41
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 65 42
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 65 43
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 65 44
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 65 45
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates18 5
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 65 46
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 65 47
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 65 48
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 58
  },
  {
    rectangle := generatorPartitionRectangles 65 49
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 65 50
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 65 51
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 56
  },
  {
    rectangle := generatorPartitionRectangles 65 52
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 65 53
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates18 5
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 65 54
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates18 4
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 65 55
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates18 3
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 65 56
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates18 4
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 65 57
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 65 58
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 65 59
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 65 60
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 65 61
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 65 62
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 65 63
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks65_valid : ∀ i, (generatorLeafBlocks65 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks65 i).coordinateU.IsValid ∧
      (generatorLeafBlocks65 i).coordinateV.IsValid ∧
      (generatorLeafBlocks65 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 60⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 58⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 58⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 56⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 2 49⟩
  have hMeta : ∀ i, (generatorLeafBlocks65 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks65 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
