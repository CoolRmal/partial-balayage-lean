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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
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

/-- Actual source leaf candidates, block 39 of the recorded finite partition. -/
def generatorLeafBlocks39 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 39 0
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates42 6
    terms := 0
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 39 1
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates42 5
    terms := 1
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 39 2
    coordinateU := generatorCoordinates53 3
    coordinateV := generatorCoordinates44 0
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 39 3
    coordinateU := generatorCoordinates54 5
    coordinateV := generatorCoordinates45 6
    terms := 20
    radialRoot := generatorRadialRoots 4 55
  },
  {
    rectangle := generatorPartitionRectangles 39 4
    coordinateU := generatorCoordinates54 5
    coordinateV := generatorCoordinates45 5
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 39 5
    coordinateU := generatorCoordinates54 4
    coordinateV := generatorCoordinates45 6
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 39 6
    coordinateU := generatorCoordinates54 4
    coordinateV := generatorCoordinates45 5
    terms := 30
    radialRoot := generatorRadialRoots 4 53
  },
  {
    rectangle := generatorPartitionRectangles 39 7
    coordinateU := generatorCoordinates53 2
    coordinateV := generatorCoordinates44 0
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 39 8
    coordinateU := generatorCoordinates54 3
    coordinateV := generatorCoordinates45 6
    terms := 20
    radialRoot := generatorRadialRoots 4 53
  },
  {
    rectangle := generatorPartitionRectangles 39 9
    coordinateU := generatorCoordinates54 3
    coordinateV := generatorCoordinates45 5
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 39 10
    coordinateU := generatorCoordinates54 2
    coordinateV := generatorCoordinates45 6
    terms := 12
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 39 11
    coordinateU := generatorCoordinates54 2
    coordinateV := generatorCoordinates45 5
    terms := 12
    radialRoot := generatorRadialRoots 4 49
  },
  {
    rectangle := generatorPartitionRectangles 39 12
    coordinateU := generatorCoordinates54 5
    coordinateV := generatorCoordinates45 4
    terms := 30
    radialRoot := generatorRadialRoots 4 53
  },
  {
    rectangle := generatorPartitionRectangles 39 13
    coordinateU := generatorCoordinates54 5
    coordinateV := generatorCoordinates45 3
    terms := 30
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 39 14
    coordinateU := generatorCoordinates55 1
    coordinateV := generatorCoordinates46 0
    terms := 20
    radialRoot := generatorRadialRoots 4 52
  },
  {
    rectangle := generatorPartitionRectangles 39 15
    coordinateU := generatorCoordinates55 1
    coordinateV := generatorCoordinates45 7
    terms := 30
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 39 16
    coordinateU := generatorCoordinates55 0
    coordinateV := generatorCoordinates46 0
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 39 17
    coordinateU := generatorCoordinates55 0
    coordinateV := generatorCoordinates45 7
    terms := 20
    radialRoot := generatorRadialRoots 4 50
  },
  {
    rectangle := generatorPartitionRectangles 39 18
    coordinateU := generatorCoordinates54 4
    coordinateV := generatorCoordinates45 3
    terms := 30
    radialRoot := generatorRadialRoots 4 49
  },
  {
    rectangle := generatorPartitionRectangles 39 19
    coordinateU := generatorCoordinates54 5
    coordinateV := generatorCoordinates45 2
    terms := 30
    radialRoot := generatorRadialRoots 4 49
  },
  {
    rectangle := generatorPartitionRectangles 39 20
    coordinateU := generatorCoordinates54 5
    coordinateV := generatorCoordinates45 1
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 39 21
    coordinateU := generatorCoordinates54 4
    coordinateV := generatorCoordinates45 2
    terms := 30
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 39 22
    coordinateU := generatorCoordinates54 4
    coordinateV := generatorCoordinates45 1
    terms := 20
    radialRoot := generatorRadialRoots 4 47
  },
  {
    rectangle := generatorPartitionRectangles 39 23
    coordinateU := generatorCoordinates54 3
    coordinateV := generatorCoordinates45 4
    terms := 20
    radialRoot := generatorRadialRoots 4 49
  },
  {
    rectangle := generatorPartitionRectangles 39 24
    coordinateU := generatorCoordinates54 3
    coordinateV := generatorCoordinates45 3
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 39 25
    coordinateU := generatorCoordinates54 2
    coordinateV := generatorCoordinates45 4
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 39 26
    coordinateU := generatorCoordinates54 2
    coordinateV := generatorCoordinates45 3
    terms := 20
    radialRoot := generatorRadialRoots 4 47
  },
  {
    rectangle := generatorPartitionRectangles 39 27
    coordinateU := generatorCoordinates54 3
    coordinateV := generatorCoordinates45 2
    terms := 20
    radialRoot := generatorRadialRoots 4 47
  },
  {
    rectangle := generatorPartitionRectangles 39 28
    coordinateU := generatorCoordinates54 3
    coordinateV := generatorCoordinates45 1
    terms := 20
    radialRoot := generatorRadialRoots 4 46
  },
  {
    rectangle := generatorPartitionRectangles 39 29
    coordinateU := generatorCoordinates54 2
    coordinateV := generatorCoordinates45 2
    terms := 20
    radialRoot := generatorRadialRoots 4 46
  },
  {
    rectangle := generatorPartitionRectangles 39 30
    coordinateU := generatorCoordinates54 2
    coordinateV := generatorCoordinates45 1
    terms := 20
    radialRoot := generatorRadialRoots 4 45
  },
  {
    rectangle := generatorPartitionRectangles 39 31
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates44 0
    terms := 8
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 39 32
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates43 7
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 39 33
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates44 0
    terms := 5
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 39 34
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates43 7
    terms := 8
    radialRoot := generatorRadialRoots 4 46
  },
  {
    rectangle := generatorPartitionRectangles 39 35
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates43 6
    terms := 20
    radialRoot := generatorRadialRoots 4 46
  },
  {
    rectangle := generatorPartitionRectangles 39 36
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates43 5
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 39 37
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates43 6
    terms := 8
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 39 38
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates43 5
    terms := 8
    radialRoot := generatorRadialRoots 4 43
  },
  {
    rectangle := generatorPartitionRectangles 39 39
    coordinateU := generatorCoordinates53 3
    coordinateV := generatorCoordinates43 4
    terms := 30
    radialRoot := generatorRadialRoots 4 46
  },
  {
    rectangle := generatorPartitionRectangles 39 40
    coordinateU := generatorCoordinates53 3
    coordinateV := generatorCoordinates43 3
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 39 41
    coordinateU := generatorCoordinates53 2
    coordinateV := generatorCoordinates43 4
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 39 42
    coordinateU := generatorCoordinates53 2
    coordinateV := generatorCoordinates43 3
    terms := 12
    radialRoot := generatorRadialRoots 4 43
  },
  {
    rectangle := generatorPartitionRectangles 39 43
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates42 1
    terms := 20
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 39 44
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates43 4
    terms := 12
    radialRoot := generatorRadialRoots 4 43
  },
  {
    rectangle := generatorPartitionRectangles 39 45
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates43 3
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 39 46
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates43 4
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 39 47
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates43 3
    terms := 8
    radialRoot := generatorRadialRoots 4 41
  },
  {
    rectangle := generatorPartitionRectangles 39 48
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates43 2
    terms := 12
    radialRoot := generatorRadialRoots 4 41
  },
  {
    rectangle := generatorPartitionRectangles 39 49
    coordinateU := generatorCoordinates53 1
    coordinateV := generatorCoordinates43 1
    terms := 8
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 39 50
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates43 2
    terms := 8
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 39 51
    coordinateU := generatorCoordinates53 0
    coordinateV := generatorCoordinates43 1
    terms := 8
    radialRoot := generatorRadialRoots 4 39
  },
  {
    rectangle := generatorPartitionRectangles 39 52
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates42 4
    terms := 8
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 39 53
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates42 3
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 39 54
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates42 4
    terms := 2
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 39 55
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates42 3
    terms := 5
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 39 56
    coordinateU := generatorCoordinates52 7
    coordinateV := generatorCoordinates43 4
    terms := 5
    radialRoot := generatorRadialRoots 4 41
  },
  {
    rectangle := generatorPartitionRectangles 39 57
    coordinateU := generatorCoordinates52 7
    coordinateV := generatorCoordinates43 3
    terms := 8
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 39 58
    coordinateU := generatorCoordinates52 6
    coordinateV := generatorCoordinates43 4
    terms := 3
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 39 59
    coordinateU := generatorCoordinates52 6
    coordinateV := generatorCoordinates43 3
    terms := 4
    radialRoot := generatorRadialRoots 4 39
  },
  {
    rectangle := generatorPartitionRectangles 39 60
    coordinateU := generatorCoordinates52 7
    coordinateV := generatorCoordinates43 2
    terms := 8
    radialRoot := generatorRadialRoots 4 39
  },
  {
    rectangle := generatorPartitionRectangles 39 61
    coordinateU := generatorCoordinates52 7
    coordinateV := generatorCoordinates43 1
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 39 62
    coordinateU := generatorCoordinates52 6
    coordinateV := generatorCoordinates43 2
    terms := 5
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 39 63
    coordinateU := generatorCoordinates52 6
    coordinateV := generatorCoordinates43 1
    terms := 8
    radialRoot := generatorRadialRoots 4 37
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks39_valid : ∀ i, (generatorLeafBlocks39 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks39 i).coordinateU.IsValid ∧
      (generatorLeafBlocks39 i).coordinateV.IsValid ∧
      (generatorLeafBlocks39 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates42_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates42_valid 5, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates53_valid 3,
        generatorCoordinates44_valid 0, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates54_valid 5,
        generatorCoordinates45_valid 6, generatorRadialRoots_valid 4 55⟩
    · exact ⟨generatorCoordinates54_valid 5,
        generatorCoordinates45_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates54_valid 4,
        generatorCoordinates45_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates54_valid 4,
        generatorCoordinates45_valid 5, generatorRadialRoots_valid 4 53⟩
    · exact ⟨generatorCoordinates53_valid 2,
        generatorCoordinates44_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates54_valid 3,
        generatorCoordinates45_valid 6, generatorRadialRoots_valid 4 53⟩
    · exact ⟨generatorCoordinates54_valid 3,
        generatorCoordinates45_valid 5, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates54_valid 2,
        generatorCoordinates45_valid 6, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates54_valid 2,
        generatorCoordinates45_valid 5, generatorRadialRoots_valid 4 49⟩
    · exact ⟨generatorCoordinates54_valid 5,
        generatorCoordinates45_valid 4, generatorRadialRoots_valid 4 53⟩
    · exact ⟨generatorCoordinates54_valid 5,
        generatorCoordinates45_valid 3, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates55_valid 1,
        generatorCoordinates46_valid 0, generatorRadialRoots_valid 4 52⟩
    · exact ⟨generatorCoordinates55_valid 1,
        generatorCoordinates45_valid 7, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates55_valid 0,
        generatorCoordinates46_valid 0, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates55_valid 0,
        generatorCoordinates45_valid 7, generatorRadialRoots_valid 4 50⟩
    · exact ⟨generatorCoordinates54_valid 4,
        generatorCoordinates45_valid 3, generatorRadialRoots_valid 4 49⟩
    · exact ⟨generatorCoordinates54_valid 5,
        generatorCoordinates45_valid 2, generatorRadialRoots_valid 4 49⟩
    · exact ⟨generatorCoordinates54_valid 5,
        generatorCoordinates45_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates54_valid 4,
        generatorCoordinates45_valid 2, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates54_valid 4,
        generatorCoordinates45_valid 1, generatorRadialRoots_valid 4 47⟩
    · exact ⟨generatorCoordinates54_valid 3,
        generatorCoordinates45_valid 4, generatorRadialRoots_valid 4 49⟩
    · exact ⟨generatorCoordinates54_valid 3,
        generatorCoordinates45_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates54_valid 2,
        generatorCoordinates45_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates54_valid 2,
        generatorCoordinates45_valid 3, generatorRadialRoots_valid 4 47⟩
    · exact ⟨generatorCoordinates54_valid 3,
        generatorCoordinates45_valid 2, generatorRadialRoots_valid 4 47⟩
    · exact ⟨generatorCoordinates54_valid 3,
        generatorCoordinates45_valid 1, generatorRadialRoots_valid 4 46⟩
    · exact ⟨generatorCoordinates54_valid 2,
        generatorCoordinates45_valid 2, generatorRadialRoots_valid 4 46⟩
    · exact ⟨generatorCoordinates54_valid 2,
        generatorCoordinates45_valid 1, generatorRadialRoots_valid 4 45⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates44_valid 0, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates43_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates44_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates43_valid 7, generatorRadialRoots_valid 4 46⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates43_valid 6, generatorRadialRoots_valid 4 46⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates43_valid 5, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates43_valid 6, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates43_valid 5, generatorRadialRoots_valid 4 43⟩
    · exact ⟨generatorCoordinates53_valid 3,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 46⟩
    · exact ⟨generatorCoordinates53_valid 3,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates53_valid 2,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates53_valid 2,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 43⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates42_valid 1, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 43⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 41⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 41⟩
    · exact ⟨generatorCoordinates53_valid 1,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates53_valid 0,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 39⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates42_valid 4, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates42_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates42_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates42_valid 3, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates52_valid 7,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 41⟩
    · exact ⟨generatorCoordinates52_valid 7,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates52_valid 6,
        generatorCoordinates43_valid 4, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates52_valid 6,
        generatorCoordinates43_valid 3, generatorRadialRoots_valid 4 39⟩
    · exact ⟨generatorCoordinates52_valid 7,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 39⟩
    · exact ⟨generatorCoordinates52_valid 7,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates52_valid 6,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates52_valid 6,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 37⟩
  have hMeta : ∀ i, (generatorLeafBlocks39 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks39 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
