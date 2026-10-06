/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
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

/-- Actual source leaf candidates, block 40 of the recorded finite partition. -/
def generatorLeafBlocks40 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 40 0
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates42 2
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 40 1
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates43 2
    terms := 3
    radialRoot := generatorRadialRoots 4 37
  },
  {
    rectangle := generatorPartitionRectangles 40 2
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates43 1
    terms := 4
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 40 3
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates43 2
    terms := 2
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 40 4
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates43 1
    terms := 3
    radialRoot := generatorRadialRoots 4 35
  },
  {
    rectangle := generatorPartitionRectangles 40 5
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates37 3
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 40 6
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates37 2
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 40 7
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates37 3
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 40 8
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates37 2
    terms := 4
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 40 9
    coordinateU := generatorCoordinates51 3
    coordinateV := generatorCoordinates37 1
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 40 10
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates37 5
    terms := 8
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 40 11
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates37 4
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 40 12
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates37 5
    terms := 8
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 40 13
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates37 4
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 40 14
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates37 1
    terms := 8
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 40 15
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates37 0
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 40 16
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates38 3
    terms := 8
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 40 17
    coordinateU := generatorCoordinates51 7
    coordinateV := generatorCoordinates38 2
    terms := 5
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 40 18
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates38 3
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 40 19
    coordinateU := generatorCoordinates51 6
    coordinateV := generatorCoordinates38 2
    terms := 8
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 40 20
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates37 2
    terms := 5
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 40 21
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates38 3
    terms := 12
    radialRoot := generatorRadialRoots 4 36
  },
  {
    rectangle := generatorPartitionRectangles 40 22
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates38 2
    terms := 8
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 40 23
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates40 3
    terms := 5
    radialRoot := generatorRadialRoots 4 35
  },
  {
    rectangle := generatorPartitionRectangles 40 24
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates40 2
    terms := 5
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 40 25
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates40 3
    terms := 4
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 40 26
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates40 2
    terms := 4
    radialRoot := generatorRadialRoots 4 33
  },
  {
    rectangle := generatorPartitionRectangles 40 27
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates40 1
    terms := 5
    radialRoot := generatorRadialRoots 4 33
  },
  {
    rectangle := generatorPartitionRectangles 40 28
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates40 0
    terms := 5
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 40 29
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates40 1
    terms := 5
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 40 30
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates40 0
    terms := 5
    radialRoot := generatorRadialRoots 4 31
  },
  {
    rectangle := generatorPartitionRectangles 40 31
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates38 1
    terms := 5
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 40 32
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates38 0
    terms := 5
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 40 33
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates38 1
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 40 34
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates38 0
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 40 35
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates37 1
    terms := 8
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 40 36
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates37 0
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 40 37
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates37 7
    terms := 8
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 40 38
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates37 6
    terms := 8
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 40 39
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates37 7
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 40 40
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates37 6
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 40 41
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates37 5
    terms := 8
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 40 42
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates37 4
    terms := 8
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 40 43
    coordinateU := generatorCoordinates51 4
    coordinateV := generatorCoordinates37 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 40 44
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates38 5
    terms := 8
    radialRoot := generatorRadialRoots 4 21
  },
  {
    rectangle := generatorPartitionRectangles 40 45
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates38 4
    terms := 8
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 40 46
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates38 5
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 40 47
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates38 4
    terms := 12
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 40 48
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates34 4
    terms := 20
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 40 49
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates34 3
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 40 50
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates34 4
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 40 51
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates34 3
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 40 52
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates36 0
    terms := 20
    radialRoot := generatorRadialRoots 4 29
  },
  {
    rectangle := generatorPartitionRectangles 40 53
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 40 54
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates36 0
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 40 55
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 27
  },
  {
    rectangle := generatorPartitionRectangles 40 56
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 27
  },
  {
    rectangle := generatorPartitionRectangles 40 57
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 40 58
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 40 59
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 25
  },
  {
    rectangle := generatorPartitionRectangles 40 60
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates34 2
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 40 61
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates34 1
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 40 62
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 40 63
    coordinateU := generatorCoordinates52 1
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks40_valid : ∀ i, (generatorLeafBlocks40 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks40 i).coordinateU.IsValid ∧
      (generatorLeafBlocks40 i).coordinateV.IsValid ∧
      (generatorLeafBlocks40 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates42_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 37⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates43_valid 2, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates43_valid 1, generatorRadialRoots_valid 4 35⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates37_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates51_valid 3,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates51_valid 7,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates51_valid 6,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates37_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates38_valid 3, generatorRadialRoots_valid 4 36⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates38_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates40_valid 3, generatorRadialRoots_valid 4 35⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates40_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates40_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates40_valid 2, generatorRadialRoots_valid 4 33⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates40_valid 1, generatorRadialRoots_valid 4 33⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates40_valid 0, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates40_valid 1, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates40_valid 0, generatorRadialRoots_valid 4 31⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates38_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates38_valid 0, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates37_valid 1, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates37_valid 0, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates37_valid 7, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates37_valid 6, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates37_valid 4, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates51_valid 4,
        generatorCoordinates37_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 21⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates38_valid 5, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates38_valid 4, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 29⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 27⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 27⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 25⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates52_valid 1,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 26⟩
  have hMeta : ∀ i, (generatorLeafBlocks40 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks40 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
