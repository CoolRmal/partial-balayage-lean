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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates66
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates68

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 16 of the recorded finite partition. -/
def generatorLeafBlocks16 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 16 0
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 16 1
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 16 2
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 16 3
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates18 4
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 16 4
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 16 5
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates14 3
    terms := 30
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 16 6
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates14 2
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 16 7
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates14 3
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 16 8
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates14 2
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 16 9
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates14 1
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 16 10
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 16 11
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates14 1
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 16 12
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 16 13
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates14 3
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 16 14
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates14 2
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 16 15
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates14 3
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 16 16
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates14 2
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 16 17
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates14 1
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 16 18
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 16 19
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates14 1
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 16 20
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 16 21
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 16 22
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 16 23
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 16 24
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 16 25
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 16 26
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates9 5
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 16 27
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 16 28
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 16 29
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 16 30
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 16 31
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 16 32
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 16 33
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 16 34
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 16 35
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates9 6
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 16 36
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates9 5
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 16 37
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 16 38
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 16 39
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 16 40
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 16 41
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 16 42
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 16 43
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 16 44
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates5 2
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 16 45
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 16 46
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 16 47
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates5 5
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 16 48
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates5 4
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 16 49
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 16 50
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 16 51
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates5 3
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 16 52
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates5 2
    terms := 20
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 16 53
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 16 54
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 16 55
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 16 56
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 16 57
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 16 58
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 16 59
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 16 60
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 3 38
  },
  {
    rectangle := generatorPartitionRectangles 16 61
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 3 36
  },
  {
    rectangle := generatorPartitionRectangles 16 62
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates0 5
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  },
  {
    rectangle := generatorPartitionRectangles 16 63
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates0 4
    terms := 12
    radialRoot := generatorRadialRoots 3 35
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks16_valid : ∀ i, (generatorLeafBlocks16 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks16 i).coordinateU.IsValid ∧
      (generatorLeafBlocks16 i).coordinateV.IsValid ∧
      (generatorLeafBlocks16 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates5_valid 2, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 3 38⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 3 36⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 3 35⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates0_valid 4, generatorRadialRoots_valid 3 35⟩
  have hMeta : ∀ i, (generatorLeafBlocks16 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks16 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
