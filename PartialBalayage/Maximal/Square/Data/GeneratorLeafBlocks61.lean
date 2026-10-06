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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
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

/-- Actual source leaf candidates, block 61 of the recorded finite partition. -/
def generatorLeafBlocks61 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 61 0
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 61 1
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 61 2
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 61 3
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 61 4
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 61 5
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates9 6
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 61 6
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 61 7
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 61 8
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 61 9
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates6 5
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 61 10
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates6 4
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 61 11
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates6 5
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 61 12
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates6 4
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 61 13
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates6 3
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 61 14
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates6 2
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 61 15
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates6 3
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 61 16
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates6 2
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 61 17
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates5 5
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 61 18
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates5 4
    terms := 5
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 61 19
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 61 20
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 61 21
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 61 22
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 61 23
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 61 24
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates5 3
    terms := 4
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 61 25
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 61 26
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 61 27
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 61 28
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 61 29
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates5 5
    terms := 5
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 61 30
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates5 4
    terms := 5
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 61 31
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 61 32
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 61 33
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 61 34
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 61 35
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 61 36
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 61 37
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 61 38
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates5 3
    terms := 5
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 61 39
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 61 40
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 61 41
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates5 7
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 61 42
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates5 6
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 61 43
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 61 44
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 61 45
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 61 46
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates1 5
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 61 47
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 61 48
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 61 49
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 61 50
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 61 51
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 61 52
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 61 53
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates1 6
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 61 54
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates1 5
    terms := 4
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 61 55
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 61 56
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 61 57
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates1 4
    terms := 4
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 61 58
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates1 3
    terms := 4
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 61 59
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 61 60
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 61 61
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates1 2
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 61 62
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates1 1
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 61 63
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates0 3
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks61_valid : ∀ i, (generatorLeafBlocks61 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks61 i).coordinateU.IsValid ∧
      (generatorLeafBlocks61 i).coordinateV.IsValid ∧
      (generatorLeafBlocks61 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 13⟩
  have hMeta : ∀ i, (generatorLeafBlocks61 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks61 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
