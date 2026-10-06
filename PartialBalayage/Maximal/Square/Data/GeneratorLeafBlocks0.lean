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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates2
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates3
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates4
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates82
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates84
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates86
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates88

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 0 of the recorded finite partition. -/
def generatorLeafBlocks0 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 0 0
    coordinateU := generatorCoordinates88 7
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 1
    coordinateU := generatorCoordinates88 6
    coordinateV := generatorCoordinates0 2
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 2
    coordinateU := generatorCoordinates88 6
    coordinateV := generatorCoordinates0 1
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 0 3
    coordinateU := generatorCoordinates88 5
    coordinateV := generatorCoordinates5 0
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 4
    coordinateU := generatorCoordinates88 4
    coordinateV := generatorCoordinates5 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 5
    coordinateU := generatorCoordinates88 4
    coordinateV := generatorCoordinates5 0
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 0 6
    coordinateU := generatorCoordinates88 3
    coordinateV := generatorCoordinates0 0
    terms := 2
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 0 7
    coordinateU := generatorCoordinates88 2
    coordinateV := generatorCoordinates9 3
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 8
    coordinateU := generatorCoordinates88 1
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 9
    coordinateU := generatorCoordinates88 1
    coordinateV := generatorCoordinates9 3
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 0 10
    coordinateU := generatorCoordinates88 0
    coordinateV := generatorCoordinates4 7
    terms := 5
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 0 11
    coordinateU := generatorCoordinates88 0
    coordinateV := generatorCoordinates0 0
    terms := 20
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 0 12
    coordinateU := generatorCoordinates87 3
    coordinateV := generatorCoordinates13 6
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 13
    coordinateU := generatorCoordinates87 2
    coordinateV := generatorCoordinates13 7
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 14
    coordinateU := generatorCoordinates87 2
    coordinateV := generatorCoordinates13 6
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 0 15
    coordinateU := generatorCoordinates87 1
    coordinateV := generatorCoordinates9 2
    terms := 5
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 0 16
    coordinateU := generatorCoordinates87 3
    coordinateV := generatorCoordinates5 1
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 0 17
    coordinateU := generatorCoordinates87 3
    coordinateV := generatorCoordinates5 0
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 0 18
    coordinateU := generatorCoordinates87 2
    coordinateV := generatorCoordinates5 1
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 0 19
    coordinateU := generatorCoordinates87 2
    coordinateV := generatorCoordinates5 0
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 0 20
    coordinateU := generatorCoordinates87 3
    coordinateV := generatorCoordinates0 2
    terms := 1
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 0 21
    coordinateU := generatorCoordinates87 3
    coordinateV := generatorCoordinates0 1
    terms := 12
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 0 22
    coordinateU := generatorCoordinates87 2
    coordinateV := generatorCoordinates0 2
    terms := 5
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 0 23
    coordinateU := generatorCoordinates87 5
    coordinateV := generatorCoordinates0 4
    terms := 3
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 0 24
    coordinateU := generatorCoordinates87 5
    coordinateV := generatorCoordinates0 3
    terms := 8
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 0 25
    coordinateU := generatorCoordinates87 4
    coordinateV := generatorCoordinates0 4
    terms := 5
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 0 26
    coordinateU := generatorCoordinates87 7
    coordinateV := generatorCoordinates1 0
    terms := 5
    radialRoot := generatorRadialRoots 5 19
  },
  {
    rectangle := generatorPartitionRectangles 0 27
    coordinateU := generatorCoordinates87 7
    coordinateV := generatorCoordinates0 7
    terms := 8
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 0 28
    coordinateU := generatorCoordinates87 6
    coordinateV := generatorCoordinates1 0
    terms := 8
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 0 29
    coordinateU := generatorCoordinates87 6
    coordinateV := generatorCoordinates0 7
    terms := 20
    radialRoot := generatorRadialRoots 5 17
  },
  {
    rectangle := generatorPartitionRectangles 0 30
    coordinateU := generatorCoordinates83 2
    coordinateV := generatorCoordinates18 1
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 31
    coordinateU := generatorCoordinates83 1
    coordinateV := generatorCoordinates18 2
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 0 32
    coordinateU := generatorCoordinates83 1
    coordinateV := generatorCoordinates18 1
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 0 33
    coordinateU := generatorCoordinates83 0
    coordinateV := generatorCoordinates13 5
    terms := 5
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 0 34
    coordinateU := generatorCoordinates83 2
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 0 35
    coordinateU := generatorCoordinates83 2
    coordinateV := generatorCoordinates9 3
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 0 36
    coordinateU := generatorCoordinates83 1
    coordinateV := generatorCoordinates9 4
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 0 37
    coordinateU := generatorCoordinates83 1
    coordinateV := generatorCoordinates9 3
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 0 38
    coordinateU := generatorCoordinates83 2
    coordinateV := generatorCoordinates5 1
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 0 39
    coordinateU := generatorCoordinates83 2
    coordinateV := generatorCoordinates5 0
    terms := 2
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 0 40
    coordinateU := generatorCoordinates83 1
    coordinateV := generatorCoordinates5 1
    terms := 1
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 0 41
    coordinateU := generatorCoordinates83 4
    coordinateV := generatorCoordinates5 3
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 0 42
    coordinateU := generatorCoordinates83 4
    coordinateV := generatorCoordinates5 2
    terms := 2
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 0 43
    coordinateU := generatorCoordinates83 3
    coordinateV := generatorCoordinates5 3
    terms := 1
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 0 44
    coordinateU := generatorCoordinates83 3
    coordinateV := generatorCoordinates5 2
    terms := 8
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 0 45
    coordinateU := generatorCoordinates83 6
    coordinateV := generatorCoordinates0 6
    terms := 1
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 0 46
    coordinateU := generatorCoordinates83 6
    coordinateV := generatorCoordinates0 5
    terms := 3
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 0 47
    coordinateU := generatorCoordinates83 5
    coordinateV := generatorCoordinates0 6
    terms := 2
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 0 48
    coordinateU := generatorCoordinates83 5
    coordinateV := generatorCoordinates0 5
    terms := 5
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 0 49
    coordinateU := generatorCoordinates83 6
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 0 50
    coordinateU := generatorCoordinates84 6
    coordinateV := generatorCoordinates1 0
    terms := 12
    radialRoot := generatorRadialRoots 5 17
  },
  {
    rectangle := generatorPartitionRectangles 0 51
    coordinateU := generatorCoordinates86 0
    coordinateV := generatorCoordinates2 0
    terms := 12
    radialRoot := generatorRadialRoots 5 16
  },
  {
    rectangle := generatorPartitionRectangles 0 52
    coordinateU := generatorCoordinates86 0
    coordinateV := generatorCoordinates1 7
    terms := 20
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 0 53
    coordinateU := generatorCoordinates85 7
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 0 54
    coordinateU := generatorCoordinates85 7
    coordinateV := generatorCoordinates1 7
    terms := 20
    radialRoot := generatorRadialRoots 5 14
  },
  {
    rectangle := generatorPartitionRectangles 0 55
    coordinateU := generatorCoordinates84 5
    coordinateV := generatorCoordinates1 0
    terms := 20
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 0 56
    coordinateU := generatorCoordinates85 6
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 14
  },
  {
    rectangle := generatorPartitionRectangles 0 57
    coordinateU := generatorCoordinates85 6
    coordinateV := generatorCoordinates1 7
    terms := 30
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 0 58
    coordinateU := generatorCoordinates85 5
    coordinateV := generatorCoordinates2 0
    terms := 20
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 0 59
    coordinateU := generatorCoordinates87 0
    coordinateV := generatorCoordinates3 6
    terms := 20
    radialRoot := generatorRadialRoots 5 12
  },
  {
    rectangle := generatorPartitionRectangles 0 60
    coordinateU := generatorCoordinates87 0
    coordinateV := generatorCoordinates3 5
    terms := 20
    radialRoot := generatorRadialRoots 5 11
  },
  {
    rectangle := generatorPartitionRectangles 0 61
    coordinateU := generatorCoordinates86 7
    coordinateV := generatorCoordinates3 6
    terms := 20
    radialRoot := generatorRadialRoots 5 11
  },
  {
    rectangle := generatorPartitionRectangles 0 62
    coordinateU := generatorCoordinates86 7
    coordinateV := generatorCoordinates3 5
    terms := 30
    radialRoot := generatorRadialRoots 5 10
  },
  {
    rectangle := generatorPartitionRectangles 0 63
    coordinateU := generatorCoordinates83 5
    coordinateV := generatorCoordinates0 4
    terms := 20
    radialRoot := generatorRadialRoots 5 15
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks0_valid : ∀ i, (generatorLeafBlocks0 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks0 i).coordinateU.IsValid ∧
      (generatorLeafBlocks0 i).coordinateV.IsValid ∧
      (generatorLeafBlocks0 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates88_valid 7,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 6,
        generatorCoordinates0_valid 2, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 6,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates88_valid 5,
        generatorCoordinates5_valid 0, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 4,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 4,
        generatorCoordinates5_valid 0, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates88_valid 3,
        generatorCoordinates0_valid 0, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates88_valid 2,
        generatorCoordinates9_valid 3, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 1,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates88_valid 1,
        generatorCoordinates9_valid 3, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates88_valid 0,
        generatorCoordinates4_valid 7, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates88_valid 0,
        generatorCoordinates0_valid 0, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates87_valid 3,
        generatorCoordinates13_valid 6, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates87_valid 2,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates87_valid 2,
        generatorCoordinates13_valid 6, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates87_valid 1,
        generatorCoordinates9_valid 2, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates87_valid 3,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates87_valid 3,
        generatorCoordinates5_valid 0, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates87_valid 2,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates87_valid 2,
        generatorCoordinates5_valid 0, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates87_valid 3,
        generatorCoordinates0_valid 2, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates87_valid 3,
        generatorCoordinates0_valid 1, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates87_valid 2,
        generatorCoordinates0_valid 2, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates87_valid 5,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates87_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates87_valid 4,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates87_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 19⟩
    · exact ⟨generatorCoordinates87_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates87_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates87_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 5 17⟩
    · exact ⟨generatorCoordinates83_valid 2,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates83_valid 1,
        generatorCoordinates18_valid 2, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates83_valid 1,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates83_valid 0,
        generatorCoordinates13_valid 5, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates83_valid 2,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates83_valid 2,
        generatorCoordinates9_valid 3, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates83_valid 1,
        generatorCoordinates9_valid 4, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates83_valid 1,
        generatorCoordinates9_valid 3, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates83_valid 2,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates83_valid 2,
        generatorCoordinates5_valid 0, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates83_valid 1,
        generatorCoordinates5_valid 1, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates83_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates83_valid 4,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates83_valid 3,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates83_valid 3,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates83_valid 6,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates83_valid 6,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates83_valid 5,
        generatorCoordinates0_valid 6, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates83_valid 5,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates83_valid 6,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates84_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 17⟩
    · exact ⟨generatorCoordinates86_valid 0,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 16⟩
    · exact ⟨generatorCoordinates86_valid 0,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates85_valid 7,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates85_valid 7,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 5 14⟩
    · exact ⟨generatorCoordinates84_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates85_valid 6,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 14⟩
    · exact ⟨generatorCoordinates85_valid 6,
        generatorCoordinates1_valid 7, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates85_valid 5,
        generatorCoordinates2_valid 0, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates87_valid 0,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 12⟩
    · exact ⟨generatorCoordinates87_valid 0,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 11⟩
    · exact ⟨generatorCoordinates86_valid 7,
        generatorCoordinates3_valid 6, generatorRadialRoots_valid 5 11⟩
    · exact ⟨generatorCoordinates86_valid 7,
        generatorCoordinates3_valid 5, generatorRadialRoots_valid 5 10⟩
    · exact ⟨generatorCoordinates83_valid 5,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 5 15⟩
  have hMeta : ∀ i, (generatorLeafBlocks0 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks0 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
