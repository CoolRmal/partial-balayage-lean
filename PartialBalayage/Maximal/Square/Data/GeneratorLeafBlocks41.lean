/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
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

/-- Actual source leaf candidates, block 41 of the recorded finite partition. -/
def generatorLeafBlocks41 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 41 0
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 41 1
    coordinateU := generatorCoordinates52 0
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 41 2
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates33 3
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 41 3
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 25
  },
  {
    rectangle := generatorPartitionRectangles 41 4
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 41 5
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 41 6
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 23
  },
  {
    rectangle := generatorPartitionRectangles 41 7
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates35 2
    terms := 20
    radialRoot := generatorRadialRoots 4 23
  },
  {
    rectangle := generatorPartitionRectangles 41 8
    coordinateU := generatorCoordinates53 7
    coordinateV := generatorCoordinates35 1
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 41 9
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates35 2
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 41 10
    coordinateU := generatorCoordinates53 6
    coordinateV := generatorCoordinates35 1
    terms := 20
    radialRoot := generatorRadialRoots 4 21
  },
  {
    rectangle := generatorPartitionRectangles 41 11
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates34 0
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 41 12
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates33 7
    terms := 20
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 41 13
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates33 6
    terms := 20
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 41 14
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates33 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 41 15
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 41 16
    coordinateU := generatorCoordinates52 2
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 41 17
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates33 2
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 41 18
    coordinateU := generatorCoordinates51 2
    coordinateV := generatorCoordinates33 1
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 41 19
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates33 4
    terms := 30
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 41 20
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates33 3
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 41 21
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates34 4
    terms := 12
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 41 22
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates34 3
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 41 23
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates36 4
    terms := 8
    radialRoot := generatorRadialRoots 4 19
  },
  {
    rectangle := generatorPartitionRectangles 41 24
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates36 3
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 41 25
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates36 4
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 41 26
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates36 3
    terms := 12
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 41 27
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates36 2
    terms := 12
    radialRoot := generatorRadialRoots 4 15
  },
  {
    rectangle := generatorPartitionRectangles 41 28
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates36 1
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 41 29
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates36 2
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 41 30
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates36 1
    terms := 12
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 41 31
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates34 2
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 41 32
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates34 1
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 41 33
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates36 0
    terms := 12
    radialRoot := generatorRadialRoots 4 11
  },
  {
    rectangle := generatorPartitionRectangles 41 34
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 7
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 41 35
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates36 0
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 41 36
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 7
    terms := 20
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 41 37
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 6
    terms := 12
    radialRoot := generatorRadialRoots 4 8
  },
  {
    rectangle := generatorPartitionRectangles 41 38
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 5
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 41 39
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 6
    terms := 20
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 41 40
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 5
    terms := 20
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 41 41
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates33 2
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 41 42
    coordinateU := generatorCoordinates51 1
    coordinateV := generatorCoordinates33 1
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 41 43
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 41 44
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 41 45
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 4
    terms := 12
    radialRoot := generatorRadialRoots 4 6
  },
  {
    rectangle := generatorPartitionRectangles 41 46
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 3
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 41 47
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 4
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 41 48
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 3
    terms := 20
    radialRoot := generatorRadialRoots 4 4
  },
  {
    rectangle := generatorPartitionRectangles 41 49
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 2
    terms := 12
    radialRoot := generatorRadialRoots 4 4
  },
  {
    rectangle := generatorPartitionRectangles 41 50
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 1
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 41 51
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 2
    terms := 20
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 41 52
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 1
    terms := 20
    radialRoot := generatorRadialRoots 4 2
  },
  {
    rectangle := generatorPartitionRectangles 41 53
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates33 6
    terms := 12
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 41 54
    coordinateU := generatorCoordinates51 5
    coordinateV := generatorCoordinates33 5
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 41 55
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 4 2
  },
  {
    rectangle := generatorPartitionRectangles 41 56
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates34 7
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 41 57
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates35 0
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 41 58
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates34 7
    terms := 12
    radialRoot := generatorRadialRoots 4 0
  },
  {
    rectangle := generatorPartitionRectangles 41 59
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates34 6
    terms := 12
    radialRoot := generatorRadialRoots 4 0
  },
  {
    rectangle := generatorPartitionRectangles 41 60
    coordinateU := generatorCoordinates52 5
    coordinateV := generatorCoordinates34 5
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 41 61
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates34 6
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 41 62
    coordinateU := generatorCoordinates52 4
    coordinateV := generatorCoordinates34 5
    terms := 12
    radialRoot := generatorRadialRoots 3 62
  },
  {
    rectangle := generatorPartitionRectangles 41 63
    coordinateU := generatorCoordinates52 3
    coordinateV := generatorCoordinates30 5
    terms := 20
    radialRoot := generatorRadialRoots 4 13
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks41_valid : ∀ i, (generatorLeafBlocks41 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks41 i).coordinateU.IsValid ∧
      (generatorLeafBlocks41 i).coordinateV.IsValid ∧
      (generatorLeafBlocks41 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates52_valid 0,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 25⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 23⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 4 23⟩
    · exact ⟨generatorCoordinates53_valid 7,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates53_valid 6,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 4 21⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates52_valid 2,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates51_valid 2,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates33_valid 4, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates33_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates34_valid 4, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates34_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 19⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates36_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates36_valid 3, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates36_valid 2, generatorRadialRoots_valid 4 15⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates36_valid 1, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates36_valid 2, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates36_valid 1, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates34_valid 2, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates34_valid 1, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 11⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates36_valid 0, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 7, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 8⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 6, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 5, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates33_valid 2, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates51_valid 1,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 6⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 4, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 3, generatorRadialRoots_valid 4 4⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 4 4⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 2, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 1, generatorRadialRoots_valid 4 2⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates33_valid 6, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates51_valid 5,
        generatorCoordinates33_valid 5, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 4 2⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates35_valid 0, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates34_valid 7, generatorRadialRoots_valid 4 0⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 4 0⟩
    · exact ⟨generatorCoordinates52_valid 5,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates34_valid 6, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates52_valid 4,
        generatorCoordinates34_valid 5, generatorRadialRoots_valid 3 62⟩
    · exact ⟨generatorCoordinates52_valid 3,
        generatorCoordinates30_valid 5, generatorRadialRoots_valid 4 13⟩
  have hMeta : ∀ i, (generatorLeafBlocks41 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks41 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
