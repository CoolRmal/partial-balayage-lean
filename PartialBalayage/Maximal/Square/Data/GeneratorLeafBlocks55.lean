/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates0
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates1
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates44
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 55 of the recorded finite partition. -/
def generatorLeafBlocks55 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 55 0
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 55 1
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 55 2
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 55 3
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 55 4
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 55 5
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates1 2
    terms := 4
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 55 6
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 55 7
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 55 8
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 55 9
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 55 10
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 55 11
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 55 12
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 55 13
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 55 14
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 55 15
    coordinateU := generatorCoordinates41 4
    coordinateV := generatorCoordinates41 4
    terms := 0
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 55 16
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates41 6
    terms := 0
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 55 17
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates41 5
    terms := 0
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 55 18
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates41 6
    terms := 0
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 55 19
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates41 5
    terms := 0
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 55 20
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 55 21
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates41 7
    terms := 0
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 55 22
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 55 23
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates41 7
    terms := 0
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 55 24
    coordinateU := generatorCoordinates41 3
    coordinateV := generatorCoordinates41 3
    terms := 0
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 55 25
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates37 3
    terms := 0
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 55 26
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates37 2
    terms := 0
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 55 27
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates37 3
    terms := 0
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 55 28
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates37 2
    terms := 0
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 55 29
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates37 1
    terms := 3
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 55 30
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates37 5
    terms := 1
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 55 31
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates37 4
    terms := 2
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 55 32
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates37 5
    terms := 1
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 55 33
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates37 4
    terms := 1
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 55 34
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 55 35
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates37 0
    terms := 3
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 55 36
    coordinateU := generatorCoordinates41 3
    coordinateV := generatorCoordinates36 7
    terms := 0
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 55 37
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 55 38
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates37 0
    terms := 1
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 55 39
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates37 1
    terms := 0
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 55 40
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates37 0
    terms := 0
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 55 41
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates34 4
    terms := 3
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 55 42
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates34 3
    terms := 4
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 55 43
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates34 4
    terms := 2
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 55 44
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates34 3
    terms := 3
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 55 45
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates34 2
    terms := 8
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 55 46
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates34 1
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 55 47
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates34 2
    terms := 5
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 55 48
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates34 1
    terms := 8
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 55 49
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates34 4
    terms := 1
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 55 50
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates34 3
    terms := 2
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 55 51
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates34 4
    terms := 1
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 55 52
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates34 3
    terms := 2
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 55 53
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates34 2
    terms := 4
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 55 54
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates34 1
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 55 55
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates34 2
    terms := 3
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 55 56
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates34 1
    terms := 8
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 55 57
    coordinateU := generatorCoordinates45 0
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 53
  },
  {
    rectangle := generatorPartitionRectangles 55 58
    coordinateU := generatorCoordinates45 0
    coordinateV := generatorCoordinates35 3
    terms := 8
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 55 59
    coordinateU := generatorCoordinates44 7
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 55 60
    coordinateU := generatorCoordinates44 7
    coordinateV := generatorCoordinates35 3
    terms := 8
    radialRoot := generatorRadialRoots 3 51
  },
  {
    rectangle := generatorPartitionRectangles 55 61
    coordinateU := generatorCoordinates45 0
    coordinateV := generatorCoordinates35 2
    terms := 8
    radialRoot := generatorRadialRoots 3 51
  },
  {
    rectangle := generatorPartitionRectangles 55 62
    coordinateU := generatorCoordinates45 0
    coordinateV := generatorCoordinates35 1
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 55 63
    coordinateU := generatorCoordinates44 7
    coordinateV := generatorCoordinates35 2
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks55_valid : ∀ i, (generatorLeafBlocks55 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks55 i).coordinateU.IsValid ∧
      (generatorLeafBlocks55 i).coordinateV.IsValid ∧
      (generatorLeafBlocks55 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates41_valid 4,
        generatorCoordinates41_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates41_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates41_valid 3,
        generatorCoordinates41_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates41_valid 3,
        generatorCoordinates36_valid 7, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates45_valid 0,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 53⟩
    · exact ⟨generatorCoordinates45_valid 0,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates44_valid 7,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates44_valid 7,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 51⟩
    · exact ⟨generatorCoordinates45_valid 0,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 51⟩
    · exact ⟨generatorCoordinates45_valid 0,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates44_valid 7,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 50⟩
  have hMeta : ∀ i, (generatorLeafBlocks55 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks55 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
