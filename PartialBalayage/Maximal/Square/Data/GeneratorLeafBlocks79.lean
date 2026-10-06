/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates1
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
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

/-- Actual source leaf candidates, block 79 of the recorded finite partition. -/
def generatorLeafBlocks79 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 79 0
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 79 1
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 79 2
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 79 3
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 79 4
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 79 5
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 79 6
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 79 7
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 79 8
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates6 2
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 79 9
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 79 10
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates6 2
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 79 11
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 79 12
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 79 13
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 79 14
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 79 15
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 79 16
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates6 2
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 79 17
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 79 18
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates6 2
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 79 19
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 79 20
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates5 7
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 79 21
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates5 6
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 79 22
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates5 7
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 79 23
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates5 6
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 79 24
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates5 3
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 79 25
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates5 7
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 79 26
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates5 6
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 79 27
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates5 7
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 79 28
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates5 6
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 79 29
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 79 30
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 79 31
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 79 32
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 79 33
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 79 34
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates6 2
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 79 35
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 79 36
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates6 2
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 79 37
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 79 38
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 79 39
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 79 40
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 79 41
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 79 42
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 79 43
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 79 44
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 79 45
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 79 46
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates5 7
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 79 47
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates5 6
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 79 48
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 79 49
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates5 6
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 79 50
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates6 1
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 79 51
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates6 0
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 79 52
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates6 1
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 79 53
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates6 0
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 79 54
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 79 55
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 79 56
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 79 57
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 79 58
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 79 59
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 79 60
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 79 61
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 79 62
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 79 63
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 47
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks79_valid : ∀ i, (generatorLeafBlocks79 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks79 i).coordinateU.IsValid ∧
      (generatorLeafBlocks79 i).coordinateV.IsValid ∧
      (generatorLeafBlocks79 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 47⟩
  have hMeta : ∀ i, (generatorLeafBlocks79 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks79 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
