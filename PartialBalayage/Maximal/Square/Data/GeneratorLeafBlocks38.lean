/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates44
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 38 of the recorded finite partition. -/
def generatorLeafBlocks38 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 38 0
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates42 7
    terms := 3
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 38 1
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates43 0
    terms := 2
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 38 2
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates42 7
    terms := 4
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 38 3
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates42 6
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 38 4
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates42 5
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 38 5
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates42 6
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 38 6
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates44 2
    terms := 8
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 38 7
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates44 1
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 8
    coordinateU := generatorCoordinates53 4
    coordinateV := generatorCoordinates44 2
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 9
    coordinateU := generatorCoordinates53 4
    coordinateV := generatorCoordinates44 1
    terms := 12
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 38 10
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates42 4
    terms := 2
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 38 11
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates42 3
    terms := 3
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 38 12
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates42 4
    terms := 4
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 38 13
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates42 3
    terms := 4
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 14
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates42 2
    terms := 3
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 15
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates42 1
    terms := 4
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 16
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates42 2
    terms := 4
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 17
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates42 1
    terms := 4
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 18
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates42 4
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 19
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates42 3
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 20
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates44 0
    terms := 12
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 38 21
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates43 7
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 22
    coordinateU := generatorCoordinates53 4
    coordinateV := generatorCoordinates44 0
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 23
    coordinateU := generatorCoordinates54 7
    coordinateV := generatorCoordinates45 6
    terms := 20
    radialRoot := generatorRadialRoots 4 57
  },
  {
    rectangle := generatorPartitionRectangles 38 24
    coordinateU := generatorCoordinates54 7
    coordinateV := generatorCoordinates45 5
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 38 25
    coordinateU := generatorCoordinates54 6
    coordinateV := generatorCoordinates45 6
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 38 26
    coordinateU := generatorCoordinates54 6
    coordinateV := generatorCoordinates45 5
    terms := 20
    radialRoot := generatorRadialRoots 4 55
  },
  {
    rectangle := generatorPartitionRectangles 38 27
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates43 6
    terms := 12
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 38 28
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates43 5
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 29
    coordinateU := generatorCoordinates54 7
    coordinateV := generatorCoordinates45 4
    terms := 20
    radialRoot := generatorRadialRoots 4 55
  },
  {
    rectangle := generatorPartitionRectangles 38 30
    coordinateU := generatorCoordinates54 7
    coordinateV := generatorCoordinates45 3
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 31
    coordinateU := generatorCoordinates54 6
    coordinateV := generatorCoordinates45 4
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 32
    coordinateU := generatorCoordinates54 6
    coordinateV := generatorCoordinates45 3
    terms := 20
    radialRoot := generatorRadialRoots 4 53
  },
  {
    rectangle := generatorPartitionRectangles 38 33
    coordinateU := generatorCoordinates54 7
    coordinateV := generatorCoordinates45 2
    terms := 20
    radialRoot := generatorRadialRoots 4 53
  },
  {
    rectangle := generatorPartitionRectangles 38 34
    coordinateU := generatorCoordinates54 7
    coordinateV := generatorCoordinates45 1
    terms := 12
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 38 35
    coordinateU := generatorCoordinates54 6
    coordinateV := generatorCoordinates45 2
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 38 36
    coordinateU := generatorCoordinates54 6
    coordinateV := generatorCoordinates45 1
    terms := 20
    radialRoot := generatorRadialRoots 4 49
  },
  {
    rectangle := generatorPartitionRectangles 38 37
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates42 2
    terms := 8
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 38
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates42 1
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 38 39
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates43 4
    terms := 12
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 38 40
    coordinateU := generatorCoordinates53 5
    coordinateV := generatorCoordinates43 3
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 38 41
    coordinateU := generatorCoordinates53 4
    coordinateV := generatorCoordinates43 4
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 38 42
    coordinateU := generatorCoordinates53 4
    coordinateV := generatorCoordinates43 3
    terms := 12
    radialRoot := generatorRadialRoots 4 46
  },
  {
    rectangle := generatorPartitionRectangles 38 43
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates42 1
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 38 44
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates43 0
    terms := 1
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 38 45
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates42 7
    terms := 4
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 38 46
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates43 0
    terms := 0
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 38 47
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates42 7
    terms := 2
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 48
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates42 6
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 49
    coordinateU := generatorCoordinates53 3
    coordinateV := generatorCoordinates44 2
    terms := 8
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 38 50
    coordinateU := generatorCoordinates53 3
    coordinateV := generatorCoordinates44 1
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 51
    coordinateU := generatorCoordinates53 2
    coordinateV := generatorCoordinates44 2
    terms := 8
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 52
    coordinateU := generatorCoordinates53 2
    coordinateV := generatorCoordinates44 1
    terms := 12
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 38 53
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates42 6
    terms := 5
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 54
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates44 2
    terms := 4
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 38 55
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates44 1
    terms := 8
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 56
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates44 2
    terms := 2
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 57
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates44 1
    terms := 3
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 38 58
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates43 0
    terms := 0
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 38 59
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates42 7
    terms := 0
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 60
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates43 0
    terms := 0
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 38 61
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates42 7
    terms := 0
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 62
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates42 6
    terms := 1
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 38 63
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates42 5
    terms := 3
    radialRoot := generatorRadialRoots 4 48
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks38_valid : ∀ i, (generatorLeafBlocks38 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks38 i).coordinateU.IsValid ∧
      (generatorLeafBlocks38 i).coordinateV.IsValid ∧
      (generatorLeafBlocks38 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates42_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates43_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates42_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates42_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates42_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates42_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates44_valid 2, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates44_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates53_valid 4,
        generatorCoordinates44_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates53_valid 4,
        generatorCoordinates44_valid 1, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates42_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates42_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates42_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates42_valid 3, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates42_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates42_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates44_valid 0, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates43_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates53_valid 4,
        generatorCoordinates44_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates54_valid 7,
        generatorCoordinates45_valid 6, generatorRadialRoots_valid 4 57⟩
    · exact ⟨generatorCoordinates54_valid 7,
        generatorCoordinates45_valid 5, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates54_valid 6,
        generatorCoordinates45_valid 6, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates54_valid 6,
        generatorCoordinates45_valid 5, generatorRadialRoots_valid 4 55⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates43_valid 6, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates43_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates54_valid 7,
        generatorCoordinates45_valid 4, generatorRadialRoots_valid 4 55⟩
    · exact ⟨generatorCoordinates54_valid 7,
        generatorCoordinates45_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates54_valid 6,
        generatorCoordinates45_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates54_valid 6,
        generatorCoordinates45_valid 3, generatorRadialRoots_valid 4 53⟩
    · exact ⟨generatorCoordinates54_valid 7,
        generatorCoordinates45_valid 2, generatorRadialRoots_valid 4 53⟩
    · exact ⟨generatorCoordinates54_valid 7,
        generatorCoordinates45_valid 1, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates54_valid 6,
        generatorCoordinates45_valid 2, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates54_valid 6,
        generatorCoordinates45_valid 1, generatorRadialRoots_valid 4 49⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates53_valid 5,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates53_valid 4,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates53_valid 4,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 46⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates43_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates42_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates43_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates42_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates42_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates53_valid 3,
        generatorCoordinates44_valid 2, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates53_valid 3,
        generatorCoordinates44_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates53_valid 2,
        generatorCoordinates44_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates53_valid 2,
        generatorCoordinates44_valid 1, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates42_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates44_valid 2, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates44_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates44_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates44_valid 1, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates43_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates42_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates43_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates42_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates42_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates42_valid 5, generatorRadialRoots_valid 4 48⟩
  have hMeta : ∀ i, (generatorLeafBlocks38 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks38 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
