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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates56

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 37 of the recorded finite partition. -/
def generatorLeafBlocks37 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 37 0
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 37 1
    coordinateU := generatorCoordinates56 1
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 37 2
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates1 4
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 37 3
    coordinateU := generatorCoordinates56 0
    coordinateV := generatorCoordinates1 3
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 37 4
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 37 5
    coordinateU := generatorCoordinates55 5
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 37 6
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates0 4
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 37 7
    coordinateU := generatorCoordinates55 4
    coordinateV := generatorCoordinates0 3
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 37 8
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates51 3
    terms := 50
    radialRoot := generatorRadialRoots 5 40
  },
  {
    rectangle := generatorPartitionRectangles 37 9
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates52 1
    terms := 1
    radialRoot := generatorRadialRoots 5 39
  },
  {
    rectangle := generatorPartitionRectangles 37 10
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates52 0
    terms := 1
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 37 11
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates52 1
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 37 12
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates52 0
    terms := 0
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 37 13
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates52 3
    terms := 1
    radialRoot := generatorRadialRoots 5 39
  },
  {
    rectangle := generatorPartitionRectangles 37 14
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates52 2
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 37 15
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates52 3
    terms := 1
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 37 16
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates52 2
    terms := 0
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 37 17
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates51 2
    terms := 0
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 37 18
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates51 7
    terms := 1
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 37 19
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates51 6
    terms := 1
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 37 20
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates51 7
    terms := 0
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 37 21
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates51 6
    terms := 0
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 37 22
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates51 5
    terms := 1
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 37 23
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates51 4
    terms := 1
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 37 24
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates51 5
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 37 25
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates51 4
    terms := 0
    radialRoot := generatorRadialRoots 5 23
  },
  {
    rectangle := generatorPartitionRectangles 37 26
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates51 1
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 37 27
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates51 0
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 37 28
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates52 3
    terms := 1
    radialRoot := generatorRadialRoots 5 33
  },
  {
    rectangle := generatorPartitionRectangles 37 29
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates52 2
    terms := 0
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 37 30
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates52 3
    terms := 1
    radialRoot := generatorRadialRoots 5 29
  },
  {
    rectangle := generatorPartitionRectangles 37 31
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates52 2
    terms := 0
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 37 32
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates51 2
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 37 33
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates52 3
    terms := 1
    radialRoot := generatorRadialRoots 5 26
  },
  {
    rectangle := generatorPartitionRectangles 37 34
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates52 2
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 37 35
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates52 3
    terms := 1
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 37 36
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates52 2
    terms := 0
    radialRoot := generatorRadialRoots 5 23
  },
  {
    rectangle := generatorPartitionRectangles 37 37
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates51 2
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 37 38
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates51 1
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 37 39
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates51 0
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 37 40
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates51 1
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 37 41
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates51 0
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 37 42
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates47 7
    terms := 1
    radialRoot := generatorRadialRoots 5 23
  },
  {
    rectangle := generatorPartitionRectangles 37 43
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates47 6
    terms := 1
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 37 44
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates47 7
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 37 45
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates47 6
    terms := 0
    radialRoot := generatorRadialRoots 5 21
  },
  {
    rectangle := generatorPartitionRectangles 37 46
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates47 5
    terms := 1
    radialRoot := generatorRadialRoots 5 21
  },
  {
    rectangle := generatorPartitionRectangles 37 47
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates47 4
    terms := 1
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 37 48
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates47 5
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 37 49
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates47 4
    terms := 0
    radialRoot := generatorRadialRoots 5 19
  },
  {
    rectangle := generatorPartitionRectangles 37 50
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates46 7
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 37 51
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates46 6
    terms := 0
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 37 52
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates46 5
    terms := 12
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 37 53
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates46 4
    terms := 3
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 37 54
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates46 5
    terms := 0
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 37 55
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates46 4
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 37 56
    coordinateU := generatorCoordinates50 6
    coordinateV := generatorCoordinates46 3
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 37 57
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates46 5
    terms := 0
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 37 58
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates46 4
    terms := 2
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 37 59
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates46 5
    terms := 0
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 37 60
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates46 4
    terms := 0
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 37 61
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates42 0
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 37 62
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates41 7
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 37 63
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates43 0
    terms := 1
    radialRoot := generatorRadialRoots 5 5
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks37_valid : ∀ i, (generatorLeafBlocks37 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks37 i).coordinateU.IsValid ∧
      (generatorLeafBlocks37 i).coordinateV.IsValid ∧
      (generatorLeafBlocks37 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates56_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates56_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates55_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates55_valid 4,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates51_valid 3, generatorRadialRoots_valid 5 40⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates52_valid 1, generatorRadialRoots_valid 5 39⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates52_valid 0, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates52_valid 1, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates52_valid 0, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates52_valid 3, generatorRadialRoots_valid 5 39⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates52_valid 2, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates52_valid 3, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates52_valid 2, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates51_valid 2, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates51_valid 7, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates51_valid 6, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates51_valid 7, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates51_valid 6, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates51_valid 4, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates51_valid 5, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates51_valid 4, generatorRadialRoots_valid 5 23⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates51_valid 1, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates51_valid 0, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates52_valid 3, generatorRadialRoots_valid 5 33⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates52_valid 2, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates52_valid 3, generatorRadialRoots_valid 5 29⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates52_valid 2, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates51_valid 2, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates52_valid 3, generatorRadialRoots_valid 5 26⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates52_valid 2, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates52_valid 3, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates52_valid 2, generatorRadialRoots_valid 5 23⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates51_valid 2, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates51_valid 1, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates51_valid 0, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates51_valid 1, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates51_valid 0, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates47_valid 7, generatorRadialRoots_valid 5 23⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates47_valid 6, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates47_valid 7, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates47_valid 6, generatorRadialRoots_valid 5 21⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates47_valid 5, generatorRadialRoots_valid 5 21⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates47_valid 4, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates47_valid 5, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates47_valid 4, generatorRadialRoots_valid 5 19⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates46_valid 7, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates46_valid 6, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates50_valid 6,
        generatorCoordinates46_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates46_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates46_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates42_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates41_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates43_valid 0, generatorRadialRoots_valid 5 5⟩
  have hMeta : ∀ i, (generatorLeafBlocks37 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks37 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
