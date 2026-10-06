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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates74
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates78

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 5 of the recorded finite partition. -/
def generatorLeafBlocks5 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 5 0
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates6 3
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 5 1
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates6 2
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 5 2
    coordinateU := generatorCoordinates79 6
    coordinateV := generatorCoordinates6 7
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 5 3
    coordinateU := generatorCoordinates79 6
    coordinateV := generatorCoordinates6 6
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 5 4
    coordinateU := generatorCoordinates79 5
    coordinateV := generatorCoordinates6 7
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 5 5
    coordinateU := generatorCoordinates79 5
    coordinateV := generatorCoordinates6 6
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 5 6
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates6 0
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 5 7
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates6 1
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 5 8
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates6 0
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 5 9
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates5 7
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 5 10
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 5 11
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates5 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 5 12
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 5 13
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates5 3
    terms := 30
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 5 14
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates5 2
    terms := 30
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 5 15
    coordinateU := generatorCoordinates78 4
    coordinateV := generatorCoordinates0 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 5 16
    coordinateU := generatorCoordinates78 4
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 5 17
    coordinateU := generatorCoordinates78 3
    coordinateV := generatorCoordinates0 6
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 5 18
    coordinateU := generatorCoordinates78 3
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 5 19
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 5 20
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates1 1
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 5 21
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates1 2
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 5 22
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates1 1
    terms := 20
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 5 23
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 5 24
    coordinateU := generatorCoordinates79 4
    coordinateV := generatorCoordinates0 7
    terms := 30
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 5 25
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates1 0
    terms := 30
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 5 26
    coordinateU := generatorCoordinates79 3
    coordinateV := generatorCoordinates0 7
    terms := 50
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 5 27
    coordinateU := generatorCoordinates78 3
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 5 28
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 5 29
    coordinateU := generatorCoordinates79 2
    coordinateV := generatorCoordinates0 7
    terms := 30
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 5 30
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 5 31
    coordinateU := generatorCoordinates79 1
    coordinateV := generatorCoordinates0 7
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 5 32
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates0 6
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 5 33
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 5 34
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 5 35
    coordinateU := generatorCoordinates78 6
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 5 36
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 5 37
    coordinateU := generatorCoordinates78 5
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 5 38
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates0 5
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 5 39
    coordinateU := generatorCoordinates78 2
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 5 40
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 5 41
    coordinateU := generatorCoordinates79 0
    coordinateV := generatorCoordinates0 7
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 5 42
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 5 43
    coordinateU := generatorCoordinates78 7
    coordinateV := generatorCoordinates0 7
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 5 44
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 5 45
    coordinateU := generatorCoordinates78 1
    coordinateV := generatorCoordinates0 3
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 5 46
    coordinateU := generatorCoordinates75 3
    coordinateV := generatorCoordinates29 0
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 5 47
    coordinateU := generatorCoordinates75 2
    coordinateV := generatorCoordinates29 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 5 48
    coordinateU := generatorCoordinates75 2
    coordinateV := generatorCoordinates29 0
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 5 49
    coordinateU := generatorCoordinates75 1
    coordinateV := generatorCoordinates25 0
    terms := 8
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 5 50
    coordinateU := generatorCoordinates75 3
    coordinateV := generatorCoordinates21 5
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 5 51
    coordinateU := generatorCoordinates75 3
    coordinateV := generatorCoordinates21 4
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 5 52
    coordinateU := generatorCoordinates75 2
    coordinateV := generatorCoordinates21 5
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 5 53
    coordinateU := generatorCoordinates75 2
    coordinateV := generatorCoordinates21 4
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 5 54
    coordinateU := generatorCoordinates75 3
    coordinateV := generatorCoordinates18 2
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 5 55
    coordinateU := generatorCoordinates75 3
    coordinateV := generatorCoordinates18 1
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 5 56
    coordinateU := generatorCoordinates75 2
    coordinateV := generatorCoordinates18 2
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 5 57
    coordinateU := generatorCoordinates75 2
    coordinateV := generatorCoordinates18 1
    terms := 20
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 5 58
    coordinateU := generatorCoordinates75 3
    coordinateV := generatorCoordinates13 7
    terms := 5
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 5 59
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates14 1
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 5 60
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 5 61
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates14 1
    terms := 3
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 5 62
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 5 63
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates14 3
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks5_valid : ∀ i, (generatorLeafBlocks5 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks5 i).coordinateU.IsValid ∧
      (generatorLeafBlocks5 i).coordinateV.IsValid ∧
      (generatorLeafBlocks5 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates79_valid 6,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates79_valid 6,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates79_valid 5,
        generatorCoordinates6_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates79_valid 5,
        generatorCoordinates6_valid 6, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates78_valid 4,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates78_valid 4,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates78_valid 3,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates78_valid 3,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates79_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates79_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates78_valid 3,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates79_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates79_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates78_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates78_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates78_valid 2,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates79_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates78_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates78_valid 1,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates75_valid 3,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates75_valid 2,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates75_valid 2,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates75_valid 1,
        generatorCoordinates25_valid 0, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates75_valid 3,
        generatorCoordinates21_valid 5, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates75_valid 3,
        generatorCoordinates21_valid 4, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates75_valid 2,
        generatorCoordinates21_valid 5, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates75_valid 2,
        generatorCoordinates21_valid 4, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates75_valid 3,
        generatorCoordinates18_valid 2, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates75_valid 3,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates75_valid 2,
        generatorCoordinates18_valid 2, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates75_valid 2,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates75_valid 3,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 5 18⟩
  have hMeta : ∀ i, (generatorLeafBlocks5 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks5 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
