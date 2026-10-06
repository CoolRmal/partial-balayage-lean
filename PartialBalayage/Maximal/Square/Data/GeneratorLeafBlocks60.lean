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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 60 of the recorded finite partition. -/
def generatorLeafBlocks60 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 60 0
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 60 1
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates18 4
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 60 2
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 60 3
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates18 4
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 60 4
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 60 5
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates15 3
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 60 6
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates15 2
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 60 7
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates15 3
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 60 8
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates15 2
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 60 9
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates15 1
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 60 10
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates15 0
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 60 11
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates15 1
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 60 12
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates15 0
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 60 13
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 60 14
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 60 15
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates14 7
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 60 16
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates14 6
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 60 17
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates14 7
    terms := 5
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 60 18
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates14 6
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 60 19
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 60 20
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 60 21
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 60 22
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 60 23
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 60 24
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 60 25
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 60 26
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 60 27
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates15 3
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 60 28
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates15 2
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 60 29
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates15 3
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 60 30
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates15 2
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 60 31
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 60 32
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 60 33
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates14 5
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 60 34
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 60 35
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates14 5
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 60 36
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 60 37
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 60 38
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 60 39
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 60 40
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 60 41
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 60 42
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 60 43
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 60 44
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 60 45
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 60 46
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates10 6
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 60 47
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates10 5
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 60 48
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates10 6
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 60 49
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates10 5
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 60 50
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 60 51
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates9 7
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 60 52
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates10 4
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 60 53
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates10 3
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 60 54
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates10 4
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 60 55
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates10 3
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 60 56
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates10 2
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 60 57
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates10 1
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 60 58
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates10 2
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 60 59
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates10 1
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 60 60
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates9 6
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 60 61
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates9 5
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 60 62
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 60 63
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates9 7
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks60_valid : ∀ i, (generatorLeafBlocks60 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks60 i).coordinateU.IsValid ∧
      (generatorLeafBlocks60 i).coordinateV.IsValid ∧
      (generatorLeafBlocks60 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 43⟩
  have hMeta : ∀ i, (generatorLeafBlocks60 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks60 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
