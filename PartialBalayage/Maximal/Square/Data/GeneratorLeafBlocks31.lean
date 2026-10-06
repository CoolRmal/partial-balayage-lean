/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates48
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates56
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates58

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 31 of the recorded finite partition. -/
def generatorLeafBlocks31 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 31 0
    coordinateU := generatorCoordinates59 2
    coordinateV := generatorCoordinates50 4
    terms := 50
    radialRoot := generatorRadialRoots 5 32
  },
  {
    rectangle := generatorPartitionRectangles 31 1
    coordinateU := generatorCoordinates59 3
    coordinateV := generatorCoordinates50 3
    terms := 30
    radialRoot := generatorRadialRoots 5 32
  },
  {
    rectangle := generatorPartitionRectangles 31 2
    coordinateU := generatorCoordinates59 3
    coordinateV := generatorCoordinates50 2
    terms := 30
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 31 3
    coordinateU := generatorCoordinates59 2
    coordinateV := generatorCoordinates50 3
    terms := 50
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 31 4
    coordinateU := generatorCoordinates59 2
    coordinateV := generatorCoordinates50 2
    terms := 30
    radialRoot := generatorRadialRoots 5 30
  },
  {
    rectangle := generatorPartitionRectangles 31 5
    coordinateU := generatorCoordinates57 7
    coordinateV := generatorCoordinates49 1
    terms := 20
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 31 6
    coordinateU := generatorCoordinates57 7
    coordinateV := generatorCoordinates49 0
    terms := 12
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 31 7
    coordinateU := generatorCoordinates57 6
    coordinateV := generatorCoordinates49 1
    terms := 30
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 31 8
    coordinateU := generatorCoordinates57 6
    coordinateV := generatorCoordinates49 0
    terms := 20
    radialRoot := generatorRadialRoots 5 27
  },
  {
    rectangle := generatorPartitionRectangles 31 9
    coordinateU := generatorCoordinates59 1
    coordinateV := generatorCoordinates50 5
    terms := 75
    radialRoot := generatorRadialRoots 5 32
  },
  {
    rectangle := generatorPartitionRectangles 31 10
    coordinateU := generatorCoordinates59 1
    coordinateV := generatorCoordinates50 4
    terms := 75
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 31 11
    coordinateU := generatorCoordinates59 0
    coordinateV := generatorCoordinates50 5
    terms := 75
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 31 12
    coordinateU := generatorCoordinates59 0
    coordinateV := generatorCoordinates50 4
    terms := 75
    radialRoot := generatorRadialRoots 5 30
  },
  {
    rectangle := generatorPartitionRectangles 31 13
    coordinateU := generatorCoordinates59 1
    coordinateV := generatorCoordinates50 3
    terms := 50
    radialRoot := generatorRadialRoots 5 30
  },
  {
    rectangle := generatorPartitionRectangles 31 14
    coordinateU := generatorCoordinates59 1
    coordinateV := generatorCoordinates50 2
    terms := 30
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 31 15
    coordinateU := generatorCoordinates59 0
    coordinateV := generatorCoordinates50 3
    terms := 50
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 31 16
    coordinateU := generatorCoordinates59 0
    coordinateV := generatorCoordinates50 2
    terms := 30
    radialRoot := generatorRadialRoots 5 28
  },
  {
    rectangle := generatorPartitionRectangles 31 17
    coordinateU := generatorCoordinates58 7
    coordinateV := generatorCoordinates50 5
    terms := 50
    radialRoot := generatorRadialRoots 5 30
  },
  {
    rectangle := generatorPartitionRectangles 31 18
    coordinateU := generatorCoordinates58 7
    coordinateV := generatorCoordinates50 4
    terms := 30
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 31 19
    coordinateU := generatorCoordinates58 6
    coordinateV := generatorCoordinates50 5
    terms := 30
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 31 20
    coordinateU := generatorCoordinates58 6
    coordinateV := generatorCoordinates50 4
    terms := 30
    radialRoot := generatorRadialRoots 5 28
  },
  {
    rectangle := generatorPartitionRectangles 31 21
    coordinateU := generatorCoordinates57 4
    coordinateV := generatorCoordinates49 2
    terms := 50
    radialRoot := generatorRadialRoots 5 27
  },
  {
    rectangle := generatorPartitionRectangles 31 22
    coordinateU := generatorCoordinates57 5
    coordinateV := generatorCoordinates49 1
    terms := 30
    radialRoot := generatorRadialRoots 5 27
  },
  {
    rectangle := generatorPartitionRectangles 31 23
    coordinateU := generatorCoordinates57 5
    coordinateV := generatorCoordinates49 0
    terms := 20
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 31 24
    coordinateU := generatorCoordinates57 4
    coordinateV := generatorCoordinates49 1
    terms := 30
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 31 25
    coordinateU := generatorCoordinates57 4
    coordinateV := generatorCoordinates49 0
    terms := 20
    radialRoot := generatorRadialRoots 5 25
  },
  {
    rectangle := generatorPartitionRectangles 31 26
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates47 5
    terms := 12
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 31 27
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates47 4
    terms := 8
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 31 28
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates47 5
    terms := 20
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 31 29
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates47 4
    terms := 8
    radialRoot := generatorRadialRoots 5 23
  },
  {
    rectangle := generatorPartitionRectangles 31 30
    coordinateU := generatorCoordinates57 3
    coordinateV := generatorCoordinates49 3
    terms := 20
    radialRoot := generatorRadialRoots 5 27
  },
  {
    rectangle := generatorPartitionRectangles 31 31
    coordinateU := generatorCoordinates57 3
    coordinateV := generatorCoordinates49 2
    terms := 20
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 31 32
    coordinateU := generatorCoordinates57 2
    coordinateV := generatorCoordinates49 3
    terms := 12
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 31 33
    coordinateU := generatorCoordinates57 2
    coordinateV := generatorCoordinates49 2
    terms := 12
    radialRoot := generatorRadialRoots 5 25
  },
  {
    rectangle := generatorPartitionRectangles 31 34
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates47 6
    terms := 30
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 31 35
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates47 7
    terms := 12
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 31 36
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates47 6
    terms := 8
    radialRoot := generatorRadialRoots 5 23
  },
  {
    rectangle := generatorPartitionRectangles 31 37
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates47 5
    terms := 12
    radialRoot := generatorRadialRoots 5 23
  },
  {
    rectangle := generatorPartitionRectangles 31 38
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates47 4
    terms := 8
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 31 39
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates47 5
    terms := 8
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 31 40
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates47 4
    terms := 4
    radialRoot := generatorRadialRoots 5 21
  },
  {
    rectangle := generatorPartitionRectangles 31 41
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates46 5
    terms := 4
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 31 42
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates46 4
    terms := 1
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 31 43
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates46 5
    terms := 20
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 31 44
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates46 4
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 31 45
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 31 46
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates41 7
    terms := 1
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 31 47
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 31 48
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates41 7
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 31 49
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates41 6
    terms := 3
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 31 50
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates42 2
    terms := 3
    radialRoot := generatorRadialRoots 5 17
  },
  {
    rectangle := generatorPartitionRectangles 31 51
    coordinateU := generatorCoordinates56 7
    coordinateV := generatorCoordinates42 1
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 31 52
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates42 2
    terms := 4
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 31 53
    coordinateU := generatorCoordinates56 6
    coordinateV := generatorCoordinates42 1
    terms := 8
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 31 54
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates41 6
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 31 55
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates42 2
    terms := 4
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 31 56
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates42 1
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 31 57
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates42 2
    terms := 4
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 31 58
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates42 1
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 31 59
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates42 0
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 31 60
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates41 7
    terms := 1
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 31 61
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates42 0
    terms := 1
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 31 62
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates41 7
    terms := 1
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 31 63
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates41 6
    terms := 2
    radialRoot := generatorRadialRoots 5 9
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks31_valid : ∀ i, (generatorLeafBlocks31 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks31 i).coordinateU.IsValid ∧
      (generatorLeafBlocks31 i).coordinateV.IsValid ∧
      (generatorLeafBlocks31 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates59_valid 2,
        generatorCoordinates50_valid 4, generatorRadialRoots_valid 5 32⟩
    · exact ⟨generatorCoordinates59_valid 3,
        generatorCoordinates50_valid 3, generatorRadialRoots_valid 5 32⟩
    · exact ⟨generatorCoordinates59_valid 3,
        generatorCoordinates50_valid 2, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates59_valid 2,
        generatorCoordinates50_valid 3, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates59_valid 2,
        generatorCoordinates50_valid 2, generatorRadialRoots_valid 5 30⟩
    · exact ⟨generatorCoordinates57_valid 7,
        generatorCoordinates49_valid 1, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates57_valid 7,
        generatorCoordinates49_valid 0, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates57_valid 6,
        generatorCoordinates49_valid 1, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates57_valid 6,
        generatorCoordinates49_valid 0, generatorRadialRoots_valid 5 27⟩
    · exact ⟨generatorCoordinates59_valid 1,
        generatorCoordinates50_valid 5, generatorRadialRoots_valid 5 32⟩
    · exact ⟨generatorCoordinates59_valid 1,
        generatorCoordinates50_valid 4, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates59_valid 0,
        generatorCoordinates50_valid 5, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates59_valid 0,
        generatorCoordinates50_valid 4, generatorRadialRoots_valid 5 30⟩
    · exact ⟨generatorCoordinates59_valid 1,
        generatorCoordinates50_valid 3, generatorRadialRoots_valid 5 30⟩
    · exact ⟨generatorCoordinates59_valid 1,
        generatorCoordinates50_valid 2, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates59_valid 0,
        generatorCoordinates50_valid 3, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates59_valid 0,
        generatorCoordinates50_valid 2, generatorRadialRoots_valid 5 28⟩
    · exact ⟨generatorCoordinates58_valid 7,
        generatorCoordinates50_valid 5, generatorRadialRoots_valid 5 30⟩
    · exact ⟨generatorCoordinates58_valid 7,
        generatorCoordinates50_valid 4, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates58_valid 6,
        generatorCoordinates50_valid 5, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates58_valid 6,
        generatorCoordinates50_valid 4, generatorRadialRoots_valid 5 28⟩
    · exact ⟨generatorCoordinates57_valid 4,
        generatorCoordinates49_valid 2, generatorRadialRoots_valid 5 27⟩
    · exact ⟨generatorCoordinates57_valid 5,
        generatorCoordinates49_valid 1, generatorRadialRoots_valid 5 27⟩
    · exact ⟨generatorCoordinates57_valid 5,
        generatorCoordinates49_valid 0, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates57_valid 4,
        generatorCoordinates49_valid 1, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates57_valid 4,
        generatorCoordinates49_valid 0, generatorRadialRoots_valid 5 25⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates47_valid 5, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates47_valid 4, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates47_valid 5, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates47_valid 4, generatorRadialRoots_valid 5 23⟩
    · exact ⟨generatorCoordinates57_valid 3,
        generatorCoordinates49_valid 3, generatorRadialRoots_valid 5 27⟩
    · exact ⟨generatorCoordinates57_valid 3,
        generatorCoordinates49_valid 2, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates57_valid 2,
        generatorCoordinates49_valid 3, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates57_valid 2,
        generatorCoordinates49_valid 2, generatorRadialRoots_valid 5 25⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates47_valid 6, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates47_valid 7, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates47_valid 6, generatorRadialRoots_valid 5 23⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates47_valid 5, generatorRadialRoots_valid 5 23⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates47_valid 4, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates47_valid 5, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates47_valid 4, generatorRadialRoots_valid 5 21⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 5 17⟩
    · exact ⟨generatorCoordinates56_valid 7,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates56_valid 6,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates41_valid 6, generatorRadialRoots_valid 5 9⟩
  have hMeta : ∀ i, (generatorLeafBlocks31 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks31 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
