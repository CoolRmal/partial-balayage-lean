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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
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

/-- Actual source leaf candidates, block 85 of the recorded finite partition. -/
def generatorLeafBlocks85 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 85 0
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates10 6
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 85 1
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates10 5
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 85 2
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 85 3
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 85 4
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 85 5
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 85 6
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates9 7
    terms := 5
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 85 7
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates10 4
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 85 8
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 85 9
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates10 4
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 85 10
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 85 11
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 85 12
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 13
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 14
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 15
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 85 16
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 17
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 18
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 19
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 20
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 21
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 22
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 85 23
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 1 61
  },
  {
    rectangle := generatorPartitionRectangles 85 24
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 85 25
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates11 0
    terms := 2
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 85 26
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates10 7
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 85 27
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates10 6
    terms := 2
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 85 28
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates10 5
    terms := 3
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 29
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates10 6
    terms := 2
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 30
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates10 5
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 31
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates11 0
    terms := 1
    radialRoot := generatorRadialRoots 1 57
  },
  {
    rectangle := generatorPartitionRectangles 85 32
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 33
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates11 0
    terms := 1
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 85 34
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 35
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 36
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 37
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 38
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 85 39
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 40
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 41
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates10 4
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 42
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 85 43
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 85 44
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 85 45
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 85 46
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 85 47
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 85 48
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 85 49
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 85 50
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 85 51
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 85 52
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 85 53
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 85 54
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 85 55
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 53
  },
  {
    rectangle := generatorPartitionRectangles 85 56
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 57
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 85 58
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 85 59
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 49
  },
  {
    rectangle := generatorPartitionRectangles 85 60
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 85 61
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 85 62
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 85 63
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 1 49
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks85_valid : ∀ i, (generatorLeafBlocks85 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks85 i).coordinateU.IsValid ∧
      (generatorLeafBlocks85 i).coordinateV.IsValid ∧
      (generatorLeafBlocks85 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 61⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 57⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 53⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 49⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 49⟩
  have hMeta : ∀ i, (generatorLeafBlocks85 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks85 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
