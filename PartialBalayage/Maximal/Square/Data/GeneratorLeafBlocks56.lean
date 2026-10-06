/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates44

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 56 of the recorded finite partition. -/
def generatorLeafBlocks56 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 56 0
    coordinateU := generatorCoordinates44 7
    coordinateV := generatorCoordinates35 1
    terms := 8
    radialRoot := generatorRadialRoots 3 49
  },
  {
    rectangle := generatorPartitionRectangles 56 1
    coordinateU := generatorCoordinates44 6
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 51
  },
  {
    rectangle := generatorPartitionRectangles 56 2
    coordinateU := generatorCoordinates44 6
    coordinateV := generatorCoordinates35 3
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 56 3
    coordinateU := generatorCoordinates44 5
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 56 4
    coordinateU := generatorCoordinates44 5
    coordinateV := generatorCoordinates35 3
    terms := 12
    radialRoot := generatorRadialRoots 3 49
  },
  {
    rectangle := generatorPartitionRectangles 56 5
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates33 7
    terms := 20
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 56 6
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 56 7
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 8
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 9
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 10
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 49
  },
  {
    rectangle := generatorPartitionRectangles 56 11
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates35 3
    terms := 12
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 56 12
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 56 13
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates35 3
    terms := 12
    radialRoot := generatorRadialRoots 3 47
  },
  {
    rectangle := generatorPartitionRectangles 56 14
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates35 2
    terms := 12
    radialRoot := generatorRadialRoots 3 47
  },
  {
    rectangle := generatorPartitionRectangles 56 15
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates35 1
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 16
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates35 2
    terms := 12
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 17
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates35 1
    terms := 12
    radialRoot := generatorRadialRoots 3 45
  },
  {
    rectangle := generatorPartitionRectangles 56 18
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 47
  },
  {
    rectangle := generatorPartitionRectangles 56 19
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates35 3
    terms := 8
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 20
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates35 4
    terms := 8
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 21
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates35 3
    terms := 8
    radialRoot := generatorRadialRoots 3 45
  },
  {
    rectangle := generatorPartitionRectangles 56 22
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates35 2
    terms := 12
    radialRoot := generatorRadialRoots 3 45
  },
  {
    rectangle := generatorPartitionRectangles 56 23
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates35 1
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 24
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates35 2
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 25
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates35 1
    terms := 12
    radialRoot := generatorRadialRoots 3 43
  },
  {
    rectangle := generatorPartitionRectangles 56 26
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 3 45
  },
  {
    rectangle := generatorPartitionRectangles 56 27
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates34 7
    terms := 8
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 28
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 29
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates34 7
    terms := 8
    radialRoot := generatorRadialRoots 3 43
  },
  {
    rectangle := generatorPartitionRectangles 56 30
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates34 6
    terms := 8
    radialRoot := generatorRadialRoots 3 43
  },
  {
    rectangle := generatorPartitionRectangles 56 31
    coordinateU := generatorCoordinates44 4
    coordinateV := generatorCoordinates34 5
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 32
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates34 6
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 33
    coordinateU := generatorCoordinates44 3
    coordinateV := generatorCoordinates34 5
    terms := 8
    radialRoot := generatorRadialRoots 3 41
  },
  {
    rectangle := generatorPartitionRectangles 56 34
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 3 43
  },
  {
    rectangle := generatorPartitionRectangles 56 35
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates34 7
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 36
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 37
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates34 7
    terms := 8
    radialRoot := generatorRadialRoots 3 41
  },
  {
    rectangle := generatorPartitionRectangles 56 38
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates34 6
    terms := 8
    radialRoot := generatorRadialRoots 3 41
  },
  {
    rectangle := generatorPartitionRectangles 56 39
    coordinateU := generatorCoordinates44 2
    coordinateV := generatorCoordinates34 5
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 56 40
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates34 6
    terms := 8
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 56 41
    coordinateU := generatorCoordinates44 1
    coordinateV := generatorCoordinates34 5
    terms := 8
    radialRoot := generatorRadialRoots 3 39
  },
  {
    rectangle := generatorPartitionRectangles 56 42
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates34 4
    terms := 1
    radialRoot := generatorRadialRoots 3 52
  },
  {
    rectangle := generatorPartitionRectangles 56 43
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 56 44
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates34 4
    terms := 0
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 56 45
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 56 46
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates34 2
    terms := 2
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 56 47
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates34 1
    terms := 5
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 48
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates34 2
    terms := 2
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 49
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates34 1
    terms := 4
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 50
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates34 4
    terms := 0
    radialRoot := generatorRadialRoots 3 48
  },
  {
    rectangle := generatorPartitionRectangles 56 51
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 52
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates34 4
    terms := 0
    radialRoot := generatorRadialRoots 3 46
  },
  {
    rectangle := generatorPartitionRectangles 56 53
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates34 3
    terms := 1
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 54
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates34 2
    terms := 1
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 55
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates34 1
    terms := 3
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 56
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates34 2
    terms := 1
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 57
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates34 1
    terms := 3
    radialRoot := generatorRadialRoots 3 40
  },
  {
    rectangle := generatorPartitionRectangles 56 58
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 3 44
  },
  {
    rectangle := generatorPartitionRectangles 56 59
    coordinateU := generatorCoordinates44 0
    coordinateV := generatorCoordinates35 2
    terms := 8
    radialRoot := generatorRadialRoots 3 43
  },
  {
    rectangle := generatorPartitionRectangles 56 60
    coordinateU := generatorCoordinates44 0
    coordinateV := generatorCoordinates35 1
    terms := 12
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 61
    coordinateU := generatorCoordinates43 7
    coordinateV := generatorCoordinates35 2
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  },
  {
    rectangle := generatorPartitionRectangles 56 62
    coordinateU := generatorCoordinates43 7
    coordinateV := generatorCoordinates35 1
    terms := 8
    radialRoot := generatorRadialRoots 3 41
  },
  {
    rectangle := generatorPartitionRectangles 56 63
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates34 0
    terms := 8
    radialRoot := generatorRadialRoots 3 42
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks56_valid : ∀ i, (generatorLeafBlocks56 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks56 i).coordinateU.IsValid ∧
      (generatorLeafBlocks56 i).coordinateV.IsValid ∧
      (generatorLeafBlocks56 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates44_valid 7,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 49⟩
    · exact ⟨generatorCoordinates44_valid 6,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 51⟩
    · exact ⟨generatorCoordinates44_valid 6,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates44_valid 5,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates44_valid 5,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 49⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 49⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 47⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 47⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 45⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 47⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 3 45⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 45⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 43⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 3 45⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 3 43⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 43⟩
    · exact ⟨generatorCoordinates44_valid 4,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates44_valid 3,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 41⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 3 43⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 3 41⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 41⟩
    · exact ⟨generatorCoordinates44_valid 2,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates44_valid 1,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 39⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 52⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 48⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 3 46⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 3 40⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 44⟩
    · exact ⟨generatorCoordinates44_valid 0,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 43⟩
    · exact ⟨generatorCoordinates44_valid 0,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates43_valid 7,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 3 42⟩
    · exact ⟨generatorCoordinates43_valid 7,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 3 41⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 3 42⟩
  have hMeta : ∀ i, (generatorLeafBlocks56 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks56 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
