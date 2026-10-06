/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 44 of the recorded finite partition. -/
def generatorLeafBlocks44 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 44 0
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 44 1
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 44 2
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 44 3
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 44 4
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 44 5
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 44 6
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 44 7
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 44 8
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 44 9
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 44 10
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 44 11
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 44 12
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 44 13
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 44 14
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 44 15
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 44 16
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 44 17
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 44 18
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 44 19
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 44 20
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 44 21
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 44 22
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 44 23
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 44 24
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 44 25
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 44 26
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 44 27
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 44 28
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 44 29
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 44 30
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 44 31
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 44 32
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 44 33
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 44 34
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 44 35
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 44 36
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 44 37
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 44 38
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 44 39
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 44 40
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 44 41
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 44 42
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 44 43
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 44 44
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 44 45
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 44 46
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 44 47
    coordinateU := generatorCoordinates51 0
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 44 48
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 44 49
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 44 50
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 44 51
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 44 52
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 44 53
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 44 54
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 44 55
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 44 56
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 44 57
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates5 3
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 44 58
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates5 7
    terms := 5
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 44 59
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 44 60
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates5 7
    terms := 4
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 44 61
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates5 6
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 44 62
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 44 63
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks44_valid : ∀ i, (generatorLeafBlocks44 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks44 i).coordinateU.IsValid ∧
      (generatorLeafBlocks44 i).coordinateV.IsValid ∧
      (generatorLeafBlocks44 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates51_valid 0,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 57⟩
  have hMeta : ∀ i, (generatorLeafBlocks44 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks44 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
