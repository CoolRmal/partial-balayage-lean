/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 43 of the recorded finite partition. -/
def generatorLeafBlocks43 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 43 0
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 43 1
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 43 2
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 43 3
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 43 4
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 43 5
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 43 6
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 43 7
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 43 8
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 43 9
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 43 10
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 43 11
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 43 12
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 43 13
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 43 14
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 43 15
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 43 16
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 43 17
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 43 18
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 43 19
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates23 0
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 43 20
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 43 21
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates23 0
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 43 22
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 43 23
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 43 24
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 43 25
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 43 26
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 43 27
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 43 28
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 43 29
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 43 30
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 43 31
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 43 32
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 43 33
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 43 34
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 43 35
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 43 36
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 43 37
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 34
  },
  {
    rectangle := generatorPartitionRectangles 43 38
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 43 39
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 3 33
  },
  {
    rectangle := generatorPartitionRectangles 43 40
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 43 41
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 43 42
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 43 43
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 43 44
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 43 45
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 43 46
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 43 47
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 43 48
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 43 49
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 43 50
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 43 51
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 43 52
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 43 53
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 43 54
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 43 55
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 43 56
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 43 57
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 43 58
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 43 59
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 43 60
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 43 61
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 43 62
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 43 63
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks43_valid : ∀ i, (generatorLeafBlocks43 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks43 i).coordinateU.IsValid ∧
      (generatorLeafBlocks43 i).coordinateV.IsValid ∧
      (generatorLeafBlocks43 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 34⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 33⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 25⟩
  have hMeta : ∀ i, (generatorLeafBlocks43 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks43 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
