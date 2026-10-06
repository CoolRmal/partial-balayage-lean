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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 72 of the recorded finite partition. -/
def generatorLeafBlocks72 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 72 0
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates14 1
    terms := 5
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 72 1
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 72 2
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 72 3
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 72 4
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 72 5
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 72 6
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 72 7
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 72 8
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 72 9
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates14 2
    terms := 5
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 72 10
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 72 11
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 72 12
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 72 13
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 72 14
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 72 15
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 72 16
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 72 17
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 72 18
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates14 1
    terms := 5
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 72 19
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 72 20
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 72 21
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 72 22
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 72 23
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 72 24
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 72 25
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 72 26
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 72 27
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 72 28
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 72 29
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 72 30
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 72 31
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 72 32
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 72 33
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 72 34
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 72 35
    coordinateU := generatorCoordinates33 4
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 72 36
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 72 37
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 72 38
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 72 39
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 72 40
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates9 7
    terms := 4
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 72 41
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 72 42
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 72 43
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates10 4
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 72 44
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates10 3
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 72 45
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 72 46
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 72 47
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 72 48
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates10 1
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 72 49
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates9 6
    terms := 5
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 72 50
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates9 5
    terms := 5
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 72 51
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 72 52
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 72 53
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 72 54
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 72 55
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates9 7
    terms := 5
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 72 56
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 72 57
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 72 58
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates11 0
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 72 59
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates10 7
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 72 60
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates10 6
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 72 61
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates10 5
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 72 62
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates10 6
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 72 63
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates10 5
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks72_valid : ∀ i, (generatorLeafBlocks72 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks72 i).coordinateU.IsValid ∧
      (generatorLeafBlocks72 i).coordinateV.IsValid ∧
      (generatorLeafBlocks72 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates33_valid 4,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 2 10⟩
  have hMeta : ∀ i, (generatorLeafBlocks72 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks72 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
