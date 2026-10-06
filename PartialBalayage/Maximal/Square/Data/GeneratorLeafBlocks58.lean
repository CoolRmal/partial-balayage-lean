/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 58 of the recorded finite partition. -/
def generatorLeafBlocks58 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 58 0
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates30 1
    terms := 12
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 58 1
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates30 0
    terms := 12
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 58 2
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 58 3
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 58 4
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 58 5
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 6
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 7
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 58 8
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 58 9
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 10
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 11
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 58 12
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 58 13
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 58 14
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 58 15
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates29 6
    terms := 5
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 58 16
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 32
  },
  {
    rectangle := generatorPartitionRectangles 58 17
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 58 18
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 31
  },
  {
    rectangle := generatorPartitionRectangles 58 19
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 58 20
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 58 21
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 22
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 23
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 58 24
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 30
  },
  {
    rectangle := generatorPartitionRectangles 58 25
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 26
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 29
  },
  {
    rectangle := generatorPartitionRectangles 58 27
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 58 28
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 58 29
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 58 30
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 58 31
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 58 32
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 58 33
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 58 34
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 58 35
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 58 36
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 58 37
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 58 38
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 58 39
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 28
  },
  {
    rectangle := generatorPartitionRectangles 58 40
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 58 41
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 58 42
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 58 43
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 58 44
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates26 6
    terms := 5
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 58 45
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates26 5
    terms := 5
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 58 46
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates26 6
    terms := 5
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 58 47
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates26 5
    terms := 5
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 58 48
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates25 5
    terms := 20
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 58 49
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates25 4
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 58 50
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 58 51
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 58 52
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 58 53
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 58 54
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 58 55
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 58 56
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 58 57
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 58 58
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 58 59
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 58 60
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 58 61
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 58 62
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 58 63
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates22 7
    terms := 5
    radialRoot := generatorRadialRoots 3 20
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks58_valid : ∀ i, (generatorLeafBlocks58 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks58 i).coordinateU.IsValid ∧
      (generatorLeafBlocks58 i).coordinateV.IsValid ∧
      (generatorLeafBlocks58 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 32⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 31⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 30⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 29⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 28⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 3 20⟩
  have hMeta : ∀ i, (generatorLeafBlocks58 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks58 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
