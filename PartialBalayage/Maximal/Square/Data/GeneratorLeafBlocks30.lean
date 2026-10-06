/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates48
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52
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

/-- Actual source leaf candidates, block 30 of the recorded finite partition. -/
def generatorLeafBlocks30 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 30 0
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates51 2
    terms := 1
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 30 1
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates51 3
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 30 2
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates51 2
    terms := 3
    radialRoot := generatorRadialRoots 5 43
  },
  {
    rectangle := generatorPartitionRectangles 30 3
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates51 1
    terms := 3
    radialRoot := generatorRadialRoots 5 43
  },
  {
    rectangle := generatorPartitionRectangles 30 4
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates51 0
    terms := 8
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 30 5
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates51 1
    terms := 12
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 30 6
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates51 5
    terms := 8
    radialRoot := generatorRadialRoots 5 41
  },
  {
    rectangle := generatorPartitionRectangles 30 7
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates51 4
    terms := 8
    radialRoot := generatorRadialRoots 5 40
  },
  {
    rectangle := generatorPartitionRectangles 30 8
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates51 5
    terms := 20
    radialRoot := generatorRadialRoots 5 40
  },
  {
    rectangle := generatorPartitionRectangles 30 9
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates51 4
    terms := 20
    radialRoot := generatorRadialRoots 5 39
  },
  {
    rectangle := generatorPartitionRectangles 30 10
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates51 3
    terms := 1
    radialRoot := generatorRadialRoots 5 43
  },
  {
    rectangle := generatorPartitionRectangles 30 11
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates51 2
    terms := 5
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 30 12
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates51 3
    terms := 8
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 30 13
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates51 2
    terms := 50
    radialRoot := generatorRadialRoots 5 40
  },
  {
    rectangle := generatorPartitionRectangles 30 14
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates51 7
    terms := 8
    radialRoot := generatorRadialRoots 5 41
  },
  {
    rectangle := generatorPartitionRectangles 30 15
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates51 6
    terms := 12
    radialRoot := generatorRadialRoots 5 40
  },
  {
    rectangle := generatorPartitionRectangles 30 16
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates51 7
    terms := 8
    radialRoot := generatorRadialRoots 5 40
  },
  {
    rectangle := generatorPartitionRectangles 30 17
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates51 6
    terms := 12
    radialRoot := generatorRadialRoots 5 39
  },
  {
    rectangle := generatorPartitionRectangles 30 18
    coordinateU := generatorCoordinates56 3
    coordinateV := generatorCoordinates51 5
    terms := 50
    radialRoot := generatorRadialRoots 5 39
  },
  {
    rectangle := generatorPartitionRectangles 30 19
    coordinateU := generatorCoordinates57 7
    coordinateV := generatorCoordinates52 5
    terms := 20
    radialRoot := generatorRadialRoots 5 38
  },
  {
    rectangle := generatorPartitionRectangles 30 20
    coordinateU := generatorCoordinates57 7
    coordinateV := generatorCoordinates52 4
    terms := 30
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 21
    coordinateU := generatorCoordinates57 6
    coordinateV := generatorCoordinates52 5
    terms := 50
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 22
    coordinateU := generatorCoordinates59 3
    coordinateV := generatorCoordinates54 1
    terms := 30
    radialRoot := generatorRadialRoots 5 36
  },
  {
    rectangle := generatorPartitionRectangles 30 23
    coordinateU := generatorCoordinates59 3
    coordinateV := generatorCoordinates54 0
    terms := 30
    radialRoot := generatorRadialRoots 5 35
  },
  {
    rectangle := generatorPartitionRectangles 30 24
    coordinateU := generatorCoordinates59 2
    coordinateV := generatorCoordinates54 1
    terms := 50
    radialRoot := generatorRadialRoots 5 35
  },
  {
    rectangle := generatorPartitionRectangles 30 25
    coordinateU := generatorCoordinates59 2
    coordinateV := generatorCoordinates54 0
    terms := 50
    radialRoot := generatorRadialRoots 5 34
  },
  {
    rectangle := generatorPartitionRectangles 30 26
    coordinateU := generatorCoordinates56 2
    coordinateV := generatorCoordinates51 5
    terms := 50
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 27
    coordinateU := generatorCoordinates57 5
    coordinateV := generatorCoordinates52 5
    terms := 50
    radialRoot := generatorRadialRoots 5 35
  },
  {
    rectangle := generatorPartitionRectangles 30 28
    coordinateU := generatorCoordinates59 1
    coordinateV := generatorCoordinates54 1
    terms := 50
    radialRoot := generatorRadialRoots 5 34
  },
  {
    rectangle := generatorPartitionRectangles 30 29
    coordinateU := generatorCoordinates59 1
    coordinateV := generatorCoordinates54 0
    terms := 75
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 30
    coordinateU := generatorCoordinates59 0
    coordinateV := generatorCoordinates54 1
    terms := 50
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 31
    coordinateU := generatorCoordinates59 0
    coordinateV := generatorCoordinates54 0
    terms := 75
    radialRoot := generatorRadialRoots 5 32
  },
  {
    rectangle := generatorPartitionRectangles 30 32
    coordinateU := generatorCoordinates57 4
    coordinateV := generatorCoordinates52 5
    terms := 30
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 33
    coordinateU := generatorCoordinates58 7
    coordinateV := generatorCoordinates54 1
    terms := 30
    radialRoot := generatorRadialRoots 5 32
  },
  {
    rectangle := generatorPartitionRectangles 30 34
    coordinateU := generatorCoordinates58 7
    coordinateV := generatorCoordinates54 0
    terms := 50
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 30 35
    coordinateU := generatorCoordinates58 6
    coordinateV := generatorCoordinates54 1
    terms := 20
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 30 36
    coordinateU := generatorCoordinates58 6
    coordinateV := generatorCoordinates54 0
    terms := 30
    radialRoot := generatorRadialRoots 5 30
  },
  {
    rectangle := generatorPartitionRectangles 30 37
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates51 7
    terms := 8
    radialRoot := generatorRadialRoots 5 39
  },
  {
    rectangle := generatorPartitionRectangles 30 38
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates51 6
    terms := 12
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 39
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates51 7
    terms := 5
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 40
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates51 6
    terms := 8
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 41
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates51 5
    terms := 30
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 42
    coordinateU := generatorCoordinates57 3
    coordinateV := generatorCoordinates52 5
    terms := 20
    radialRoot := generatorRadialRoots 5 31
  },
  {
    rectangle := generatorPartitionRectangles 30 43
    coordinateU := generatorCoordinates57 3
    coordinateV := generatorCoordinates52 4
    terms := 20
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 30 44
    coordinateU := generatorCoordinates57 2
    coordinateV := generatorCoordinates52 5
    terms := 12
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 30 45
    coordinateU := generatorCoordinates57 2
    coordinateV := generatorCoordinates52 4
    terms := 12
    radialRoot := generatorRadialRoots 5 27
  },
  {
    rectangle := generatorPartitionRectangles 30 46
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates51 5
    terms := 12
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 30 47
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates51 4
    terms := 12
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 30 48
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates46 7
    terms := 8
    radialRoot := generatorRadialRoots 5 40
  },
  {
    rectangle := generatorPartitionRectangles 30 49
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates46 6
    terms := 3
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 50
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates47 7
    terms := 8
    radialRoot := generatorRadialRoots 5 39
  },
  {
    rectangle := generatorPartitionRectangles 30 51
    coordinateU := generatorCoordinates56 5
    coordinateV := generatorCoordinates47 6
    terms := 8
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 52
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates47 7
    terms := 20
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 30 53
    coordinateU := generatorCoordinates56 4
    coordinateV := generatorCoordinates47 6
    terms := 20
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 54
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates46 6
    terms := 12
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 30 55
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates46 5
    terms := 1
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 30 56
    coordinateU := generatorCoordinates55 7
    coordinateV := generatorCoordinates46 4
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 30 57
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates46 5
    terms := 2
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 30 58
    coordinateU := generatorCoordinates55 6
    coordinateV := generatorCoordinates46 4
    terms := 1
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 30 59
    coordinateU := generatorCoordinates57 7
    coordinateV := generatorCoordinates49 3
    terms := 30
    radialRoot := generatorRadialRoots 5 35
  },
  {
    rectangle := generatorPartitionRectangles 30 60
    coordinateU := generatorCoordinates57 7
    coordinateV := generatorCoordinates49 2
    terms := 30
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 61
    coordinateU := generatorCoordinates59 3
    coordinateV := generatorCoordinates50 5
    terms := 30
    radialRoot := generatorRadialRoots 5 34
  },
  {
    rectangle := generatorPartitionRectangles 30 62
    coordinateU := generatorCoordinates59 3
    coordinateV := generatorCoordinates50 4
    terms := 30
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 30 63
    coordinateU := generatorCoordinates59 2
    coordinateV := generatorCoordinates50 5
    terms := 50
    radialRoot := generatorRadialRoots 5 33
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks30_valid : ∀ i, (generatorLeafBlocks30 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks30 i).coordinateU.IsValid ∧
      (generatorLeafBlocks30 i).coordinateV.IsValid ∧
      (generatorLeafBlocks30 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates51_valid 2, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates51_valid 3, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates51_valid 2, generatorRadialRoots_valid 5 43⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates51_valid 1, generatorRadialRoots_valid 5 43⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates51_valid 0, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates51_valid 1, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 41⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates51_valid 4, generatorRadialRoots_valid 5 40⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 40⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates51_valid 4, generatorRadialRoots_valid 5 39⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates51_valid 3, generatorRadialRoots_valid 5 43⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates51_valid 2, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates51_valid 3, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates51_valid 2, generatorRadialRoots_valid 5 40⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates51_valid 7, generatorRadialRoots_valid 5 41⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates51_valid 6, generatorRadialRoots_valid 5 40⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates51_valid 7, generatorRadialRoots_valid 5 40⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates51_valid 6, generatorRadialRoots_valid 5 39⟩
    · exact ⟨generatorCoordinates56_valid 3,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 39⟩
    · exact ⟨generatorCoordinates57_valid 7,
        generatorCoordinates52_valid 5, generatorRadialRoots_valid 5 38⟩
    · exact ⟨generatorCoordinates57_valid 7,
        generatorCoordinates52_valid 4, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates57_valid 6,
        generatorCoordinates52_valid 5, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates59_valid 3,
        generatorCoordinates54_valid 1, generatorRadialRoots_valid 5 36⟩
    · exact ⟨generatorCoordinates59_valid 3,
        generatorCoordinates54_valid 0, generatorRadialRoots_valid 5 35⟩
    · exact ⟨generatorCoordinates59_valid 2,
        generatorCoordinates54_valid 1, generatorRadialRoots_valid 5 35⟩
    · exact ⟨generatorCoordinates59_valid 2,
        generatorCoordinates54_valid 0, generatorRadialRoots_valid 5 34⟩
    · exact ⟨generatorCoordinates56_valid 2,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates57_valid 5,
        generatorCoordinates52_valid 5, generatorRadialRoots_valid 5 35⟩
    · exact ⟨generatorCoordinates59_valid 1,
        generatorCoordinates54_valid 1, generatorRadialRoots_valid 5 34⟩
    · exact ⟨generatorCoordinates59_valid 1,
        generatorCoordinates54_valid 0, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates59_valid 0,
        generatorCoordinates54_valid 1, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates59_valid 0,
        generatorCoordinates54_valid 0, generatorRadialRoots_valid 5 32⟩
    · exact ⟨generatorCoordinates57_valid 4,
        generatorCoordinates52_valid 5, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates58_valid 7,
        generatorCoordinates54_valid 1, generatorRadialRoots_valid 5 32⟩
    · exact ⟨generatorCoordinates58_valid 7,
        generatorCoordinates54_valid 0, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates58_valid 6,
        generatorCoordinates54_valid 1, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates58_valid 6,
        generatorCoordinates54_valid 0, generatorRadialRoots_valid 5 30⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates51_valid 7, generatorRadialRoots_valid 5 39⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates51_valid 6, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates51_valid 7, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates51_valid 6, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates57_valid 3,
        generatorCoordinates52_valid 5, generatorRadialRoots_valid 5 31⟩
    · exact ⟨generatorCoordinates57_valid 3,
        generatorCoordinates52_valid 4, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates57_valid 2,
        generatorCoordinates52_valid 5, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates57_valid 2,
        generatorCoordinates52_valid 4, generatorRadialRoots_valid 5 27⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates51_valid 4, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates46_valid 7, generatorRadialRoots_valid 5 40⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates46_valid 6, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates47_valid 7, generatorRadialRoots_valid 5 39⟩
    · exact ⟨generatorCoordinates56_valid 5,
        generatorCoordinates47_valid 6, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates47_valid 7, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates56_valid 4,
        generatorCoordinates47_valid 6, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates46_valid 6, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates55_valid 7,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates55_valid 6,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates57_valid 7,
        generatorCoordinates49_valid 3, generatorRadialRoots_valid 5 35⟩
    · exact ⟨generatorCoordinates57_valid 7,
        generatorCoordinates49_valid 2, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates59_valid 3,
        generatorCoordinates50_valid 5, generatorRadialRoots_valid 5 34⟩
    · exact ⟨generatorCoordinates59_valid 3,
        generatorCoordinates50_valid 4, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates59_valid 2,
        generatorCoordinates50_valid 5, generatorRadialRoots_valid 5 33⟩
  have hMeta : ∀ i, (generatorLeafBlocks30 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks30 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
