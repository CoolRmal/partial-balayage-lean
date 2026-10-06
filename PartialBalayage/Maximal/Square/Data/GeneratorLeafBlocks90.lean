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

/-- Actual source leaf candidates, block 90 of the recorded finite partition. -/
def generatorLeafBlocks90 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 90 0
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates15 5
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 1
    coordinateU := generatorCoordinates24 0
    coordinateV := generatorCoordinates15 4
    terms := 1
    radialRoot := generatorRadialRoots 1 48
  },
  {
    rectangle := generatorPartitionRectangles 90 2
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates15 3
    terms := 0
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 90 3
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates15 2
    terms := 0
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 90 4
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates15 3
    terms := 0
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 90 5
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates15 2
    terms := 0
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 90 6
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates15 1
    terms := 1
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 90 7
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates15 0
    terms := 1
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 90 8
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates15 1
    terms := 0
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 90 9
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates15 0
    terms := 0
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 90 10
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates15 3
    terms := 0
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 90 11
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates15 2
    terms := 0
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 90 12
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates15 3
    terms := 0
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 90 13
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates15 2
    terms := 0
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 90 14
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates15 1
    terms := 0
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 90 15
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates15 0
    terms := 0
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 90 16
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates15 1
    terms := 0
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 90 17
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates15 0
    terms := 0
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 18
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates14 7
    terms := 1
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 90 19
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates14 6
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 90 20
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates14 7
    terms := 0
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 90 21
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates14 6
    terms := 0
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 22
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates14 5
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 23
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 24
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates14 5
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 25
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates14 4
    terms := 1
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 90 26
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates14 7
    terms := 0
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 27
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates14 6
    terms := 0
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 28
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates14 7
    terms := 0
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 29
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates14 6
    terms := 0
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 90 30
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates14 5
    terms := 0
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 90 31
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates14 4
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 90 32
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates14 5
    terms := 0
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 90 33
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates14 4
    terms := 0
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 90 34
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates11 0
    terms := 1
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 90 35
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 90 36
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates11 0
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 90 37
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 38
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 39
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 40
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 41
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 90 42
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 90 43
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 44
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 90 45
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 90 46
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates9 7
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 90 47
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 90 48
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates10 3
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 90 49
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 90 50
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates10 3
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 90 51
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 90 52
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 90 53
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 90 54
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 90 55
    coordinateU := generatorCoordinates22 0
    coordinateV := generatorCoordinates9 6
    terms := 3
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 90 56
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 90 57
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 90 58
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 90 59
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 90 60
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 90 61
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 90 62
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates11 0
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 90 63
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks90_valid : ∀ i, (generatorLeafBlocks90 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks90 i).coordinateU.IsValid ∧
      (generatorLeafBlocks90 i).coordinateV.IsValid ∧
      (generatorLeafBlocks90 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates15_valid 5, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates24_valid 0,
        generatorCoordinates15_valid 4, generatorRadialRoots_valid 1 48⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates22_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 44⟩
  have hMeta : ∀ i, (generatorLeafBlocks90 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks90 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
