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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates12
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates74
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates76

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 7 of the recorded finite partition. -/
def generatorLeafBlocks7 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 7 0
    coordinateU := generatorCoordinates77 0
    coordinateV := generatorCoordinates12 0
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 7 1
    coordinateU := generatorCoordinates77 0
    coordinateV := generatorCoordinates11 7
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 7 2
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates10 6
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 7 3
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates10 5
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 7 4
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates10 0
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 7 5
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates10 6
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 7 6
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates10 5
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 7 7
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates10 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 7 8
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates10 5
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 7 9
    coordinateU := generatorCoordinates77 1
    coordinateV := generatorCoordinates11 6
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 7 10
    coordinateU := generatorCoordinates77 1
    coordinateV := generatorCoordinates11 5
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 7 11
    coordinateU := generatorCoordinates77 0
    coordinateV := generatorCoordinates11 6
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 7 12
    coordinateU := generatorCoordinates77 0
    coordinateV := generatorCoordinates11 5
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 7 13
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates10 3
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 7 14
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates10 4
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 7 15
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates10 3
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 7 16
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates10 2
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 7 17
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates10 1
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 7 18
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates10 2
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 7 19
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates10 1
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 7 20
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates10 4
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 7 21
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates10 3
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 7 22
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates10 4
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 7 23
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates10 3
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 7 24
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 7 25
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 7 26
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 7 27
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 7 28
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 7 29
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 7 30
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates5 7
    terms := 12
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 7 31
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 7 32
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates5 7
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 7 33
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates5 6
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 7 34
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 7 35
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 7 36
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 7 37
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 7 38
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates5 5
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 7 39
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates5 4
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 7 40
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 7 41
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 7 42
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 7 43
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 7 44
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 7 45
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 7 46
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 7 47
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 7 48
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates0 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 7 49
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 7 50
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 7 51
    coordinateU := generatorCoordinates76 4
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 7 52
    coordinateU := generatorCoordinates76 4
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 7 53
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates0 5
    terms := 30
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 7 54
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 7 55
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 7 56
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 7 57
    coordinateU := generatorCoordinates75 6
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 7 58
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 7 59
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 7 60
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates1 6
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 7 61
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 7 62
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates0 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 7 63
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks7_valid : ∀ i, (generatorLeafBlocks7 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks7 i).coordinateU.IsValid ∧
      (generatorLeafBlocks7 i).coordinateV.IsValid ∧
      (generatorLeafBlocks7 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates77_valid 0,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates77_valid 0,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates77_valid 1,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates77_valid 1,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates77_valid 0,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates77_valid 0,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates76_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates76_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates75_valid 6,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 20⟩
  have hMeta : ∀ i, (generatorLeafBlocks7 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks7 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
