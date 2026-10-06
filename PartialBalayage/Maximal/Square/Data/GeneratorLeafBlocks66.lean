/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 66 of the recorded finite partition. -/
def generatorLeafBlocks66 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 66 0
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates14 2
    terms := 5
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 66 1
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 66 2
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 66 3
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 66 4
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 66 5
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 66 6
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates14 1
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 66 7
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 66 8
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 66 9
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 66 10
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 66 11
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 66 12
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 66 13
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 66 14
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 66 15
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates14 2
    terms := 5
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 66 16
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 66 17
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 66 18
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 66 19
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 66 20
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 66 21
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 66 22
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 66 23
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 66 24
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 66 25
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 66 26
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates14 7
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 66 27
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates14 6
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 66 28
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates14 7
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 66 29
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates14 6
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 66 30
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 66 31
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 66 32
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 66 33
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 66 34
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 66 35
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 66 36
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 66 37
    coordinateU := generatorCoordinates38 2
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 66 38
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 66 39
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 66 40
    coordinateU := generatorCoordinates38 1
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 66 41
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 66 42
    coordinateU := generatorCoordinates38 0
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 66 43
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates9 7
    terms := 5
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 66 44
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 66 45
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 66 46
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates9 6
    terms := 5
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 66 47
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates9 5
    terms := 5
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 66 48
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 66 49
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 66 50
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 66 51
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 66 52
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates9 7
    terms := 5
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 66 53
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 66 54
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 66 55
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 66 56
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 66 57
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 66 58
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates9 6
    terms := 5
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 66 59
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 66 60
    coordinateU := generatorCoordinates37 0
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 66 61
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates10 2
    terms := 4
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 66 62
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 66 63
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks66_valid : ∀ i, (generatorLeafBlocks66 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks66 i).coordinateU.IsValid ∧
      (generatorLeafBlocks66 i).coordinateV.IsValid ∧
      (generatorLeafBlocks66 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates38_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates38_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates38_valid 0,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates37_valid 0,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 15⟩
  have hMeta : ∀ i, (generatorLeafBlocks66 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks66 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
