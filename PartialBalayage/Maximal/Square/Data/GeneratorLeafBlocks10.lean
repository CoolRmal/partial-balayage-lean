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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates72
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates74

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 10 of the recorded finite partition. -/
def generatorLeafBlocks10 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 10 0
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates14 6
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 10 1
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 10 2
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 10 3
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 10 4
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 10 5
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 10 6
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 10 7
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates9 5
    terms := 30
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 10 8
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 10 9
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 10 10
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 10 11
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 10 12
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates10 0
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 10 13
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates9 7
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 10 14
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 10 15
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 10 16
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates9 6
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 10 17
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 10 18
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates6 5
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 10 19
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 10 20
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates6 5
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 10 21
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 10 22
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates5 4
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 10 23
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates6 5
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 10 24
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 10 25
    coordinateU := generatorCoordinates73 7
    coordinateV := generatorCoordinates6 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 10 26
    coordinateU := generatorCoordinates73 7
    coordinateV := generatorCoordinates6 4
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 10 27
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates5 4
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 10 28
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates5 3
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 10 29
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 10 30
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates5 3
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 10 31
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 10 32
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates5 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 10 33
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates5 4
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 10 34
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates5 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 10 35
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates5 4
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 10 36
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates5 3
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 10 37
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 10 38
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates5 3
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 10 39
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 10 40
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates0 6
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 10 41
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates0 5
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 10 42
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates0 6
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 10 43
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates0 5
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 10 44
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 10 45
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates1 1
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 10 46
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 10 47
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates1 1
    terms := 20
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 10 48
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates0 3
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 10 49
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 10 50
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates0 3
    terms := 20
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 10 51
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 10 52
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 10 53
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 10 54
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 10 55
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates0 5
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 10 56
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 10 57
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 10 58
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 10 59
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 10 60
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 10 61
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 10 62
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 10 63
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 3 54
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks10_valid : ∀ i, (generatorLeafBlocks10 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks10 i).coordinateU.IsValid ∧
      (generatorLeafBlocks10 i).coordinateV.IsValid ∧
      (generatorLeafBlocks10 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates73_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates73_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 54⟩
  have hMeta : ∀ i, (generatorLeafBlocks10 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks10 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
