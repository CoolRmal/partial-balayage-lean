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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 97 of the recorded finite partition. -/
def generatorLeafBlocks97 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 97 0
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 97 1
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 2
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 3
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 97 4
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 97 5
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 6
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 7
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 97 8
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 97 9
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 97 10
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 97 11
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 97 12
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 97 13
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 97 14
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 97 15
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 97 16
    coordinateU := generatorCoordinates20 0
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 97 17
    coordinateU := generatorCoordinates20 0
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 97 18
    coordinateU := generatorCoordinates19 7
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 97 19
    coordinateU := generatorCoordinates19 7
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 0 60
  },
  {
    rectangle := generatorPartitionRectangles 97 20
    coordinateU := generatorCoordinates20 0
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 60
  },
  {
    rectangle := generatorPartitionRectangles 97 21
    coordinateU := generatorCoordinates20 0
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 22
    coordinateU := generatorCoordinates19 7
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 23
    coordinateU := generatorCoordinates19 7
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 58
  },
  {
    rectangle := generatorPartitionRectangles 97 24
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates1 4
    terms := 1
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 25
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates1 3
    terms := 1
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 97 26
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 97 27
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 28
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates1 6
    terms := 0
    radialRoot := generatorRadialRoots 0 59
  },
  {
    rectangle := generatorPartitionRectangles 97 29
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates1 5
    terms := 0
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 97 30
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates1 4
    terms := 1
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 97 31
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates1 3
    terms := 1
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 97 32
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates1 4
    terms := 1
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 97 33
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates1 3
    terms := 1
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 97 34
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 57
  },
  {
    rectangle := generatorPartitionRectangles 97 35
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 97 36
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 56
  },
  {
    rectangle := generatorPartitionRectangles 97 37
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 97 38
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 97 39
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 97 40
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 97 41
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 97 42
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 55
  },
  {
    rectangle := generatorPartitionRectangles 97 43
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 97 44
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 0 54
  },
  {
    rectangle := generatorPartitionRectangles 97 45
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 97 46
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 53
  },
  {
    rectangle := generatorPartitionRectangles 97 47
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 97 48
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 0 51
  },
  {
    rectangle := generatorPartitionRectangles 97 49
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 49
  },
  {
    rectangle := generatorPartitionRectangles 97 50
    coordinateU := generatorCoordinates13 7
    coordinateV := generatorCoordinates13 7
    terms := 0
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 97 51
    coordinateU := generatorCoordinates14 3
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 97 52
    coordinateU := generatorCoordinates14 3
    coordinateV := generatorCoordinates14 0
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 97 53
    coordinateU := generatorCoordinates14 2
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 97 54
    coordinateU := generatorCoordinates14 2
    coordinateV := generatorCoordinates14 0
    terms := 0
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 97 55
    coordinateU := generatorCoordinates14 1
    coordinateV := generatorCoordinates14 3
    terms := 0
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 97 56
    coordinateU := generatorCoordinates14 1
    coordinateV := generatorCoordinates14 2
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 97 57
    coordinateU := generatorCoordinates14 0
    coordinateV := generatorCoordinates14 3
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 97 58
    coordinateU := generatorCoordinates14 0
    coordinateV := generatorCoordinates14 2
    terms := 0
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 97 59
    coordinateU := generatorCoordinates13 6
    coordinateV := generatorCoordinates13 6
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 97 60
    coordinateU := generatorCoordinates14 3
    coordinateV := generatorCoordinates10 0
    terms := 0
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 97 61
    coordinateU := generatorCoordinates14 3
    coordinateV := generatorCoordinates9 7
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 97 62
    coordinateU := generatorCoordinates14 2
    coordinateV := generatorCoordinates10 0
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 97 63
    coordinateU := generatorCoordinates14 2
    coordinateV := generatorCoordinates9 7
    terms := 0
    radialRoot := generatorRadialRoots 1 19
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks97_valid : ∀ i, (generatorLeafBlocks97 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks97 i).coordinateU.IsValid ∧
      (generatorLeafBlocks97 i).coordinateV.IsValid ∧
      (generatorLeafBlocks97 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates20_valid 0,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates20_valid 0,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates19_valid 7,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates19_valid 7,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 60⟩
    · exact ⟨generatorCoordinates20_valid 0,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 60⟩
    · exact ⟨generatorCoordinates20_valid 0,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates19_valid 7,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates19_valid 7,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 58⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 0 59⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 57⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 56⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 55⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 0 54⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 53⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 0 51⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 49⟩
    · exact ⟨generatorCoordinates13_valid 7,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates14_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates14_valid 3,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates14_valid 2,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates14_valid 2,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates14_valid 1,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates14_valid 1,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates14_valid 0,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates14_valid 0,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates13_valid 6,
        generatorCoordinates13_valid 6, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates14_valid 3,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates14_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates14_valid 2,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates14_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 1 19⟩
  have hMeta : ∀ i, (generatorLeafBlocks97 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks97 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
