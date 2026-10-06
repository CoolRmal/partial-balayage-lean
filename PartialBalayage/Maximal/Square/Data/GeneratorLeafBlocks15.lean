/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates24
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates66
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates68

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 15 of the recorded finite partition. -/
def generatorLeafBlocks15 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 15 0
    coordinateU := generatorCoordinates69 3
    coordinateV := generatorCoordinates24 2
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 15 1
    coordinateU := generatorCoordinates69 4
    coordinateV := generatorCoordinates24 1
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 15 2
    coordinateU := generatorCoordinates69 4
    coordinateV := generatorCoordinates24 0
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 15 3
    coordinateU := generatorCoordinates69 3
    coordinateV := generatorCoordinates24 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 15 4
    coordinateU := generatorCoordinates69 3
    coordinateV := generatorCoordinates24 0
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 15 5
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates22 5
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 15 6
    coordinateU := generatorCoordinates69 0
    coordinateV := generatorCoordinates22 4
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 15 7
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates22 5
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 15 8
    coordinateU := generatorCoordinates68 7
    coordinateV := generatorCoordinates22 4
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 15 9
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates21 6
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 10
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates22 5
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 15 11
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates22 4
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 12
    coordinateU := generatorCoordinates69 4
    coordinateV := generatorCoordinates23 7
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 15 13
    coordinateU := generatorCoordinates69 4
    coordinateV := generatorCoordinates23 6
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 14
    coordinateU := generatorCoordinates69 3
    coordinateV := generatorCoordinates23 7
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 15
    coordinateU := generatorCoordinates69 3
    coordinateV := generatorCoordinates23 6
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 15 16
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates22 4
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 15 17
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 15 18
    coordinateU := generatorCoordinates68 6
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 15 19
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 15 20
    coordinateU := generatorCoordinates68 5
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 15 21
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 15 22
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates23 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 15 23
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates23 1
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 15 24
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates23 0
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 15 25
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates22 7
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 15 26
    coordinateU := generatorCoordinates69 2
    coordinateV := generatorCoordinates24 1
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 15 27
    coordinateU := generatorCoordinates69 2
    coordinateV := generatorCoordinates24 0
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 28
    coordinateU := generatorCoordinates69 1
    coordinateV := generatorCoordinates24 1
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 29
    coordinateU := generatorCoordinates69 1
    coordinateV := generatorCoordinates24 0
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 15 30
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates22 7
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 31
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates22 6
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 15 32
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates22 1
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 15 33
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates22 7
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 15 34
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates22 6
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 15 35
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates22 7
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 15 36
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates22 6
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 15 37
    coordinateU := generatorCoordinates69 2
    coordinateV := generatorCoordinates23 7
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 15 38
    coordinateU := generatorCoordinates69 2
    coordinateV := generatorCoordinates23 6
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 15 39
    coordinateU := generatorCoordinates69 1
    coordinateV := generatorCoordinates23 7
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 15 40
    coordinateU := generatorCoordinates69 1
    coordinateV := generatorCoordinates23 6
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 15 41
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates22 4
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 15 42
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates22 5
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 15 43
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates22 4
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 15 44
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 15 45
    coordinateU := generatorCoordinates68 4
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 15 46
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 15 47
    coordinateU := generatorCoordinates68 3
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 15 48
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates22 5
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 15 49
    coordinateU := generatorCoordinates68 2
    coordinateV := generatorCoordinates22 4
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 15 50
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates22 5
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 15 51
    coordinateU := generatorCoordinates68 1
    coordinateV := generatorCoordinates22 4
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 15 52
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates21 6
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 15 53
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates18 6
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 15 54
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 15 55
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates18 6
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 15 56
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 15 57
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 15 58
    coordinateU := generatorCoordinates68 0
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 15 59
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 15 60
    coordinateU := generatorCoordinates67 7
    coordinateV := generatorCoordinates18 3
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 15 61
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates18 6
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 15 62
    coordinateU := generatorCoordinates67 6
    coordinateV := generatorCoordinates18 5
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 15 63
    coordinateU := generatorCoordinates67 5
    coordinateV := generatorCoordinates18 6
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks15_valid : ∀ i, (generatorLeafBlocks15 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks15 i).coordinateU.IsValid ∧
      (generatorLeafBlocks15 i).coordinateV.IsValid ∧
      (generatorLeafBlocks15 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates69_valid 3,
        generatorCoordinates24_valid 2, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates69_valid 4,
        generatorCoordinates24_valid 1, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates69_valid 4,
        generatorCoordinates24_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates69_valid 3,
        generatorCoordinates24_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates69_valid 3,
        generatorCoordinates24_valid 0, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates69_valid 0,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates68_valid 7,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates69_valid 4,
        generatorCoordinates23_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates69_valid 4,
        generatorCoordinates23_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates69_valid 3,
        generatorCoordinates23_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates69_valid 3,
        generatorCoordinates23_valid 6, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates68_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates68_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates69_valid 2,
        generatorCoordinates24_valid 1, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates69_valid 2,
        generatorCoordinates24_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates69_valid 1,
        generatorCoordinates24_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates69_valid 1,
        generatorCoordinates24_valid 0, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates69_valid 2,
        generatorCoordinates23_valid 7, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates69_valid 2,
        generatorCoordinates23_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates69_valid 1,
        generatorCoordinates23_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates69_valid 1,
        generatorCoordinates23_valid 6, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates68_valid 4,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates68_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates68_valid 2,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates68_valid 1,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates68_valid 0,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates67_valid 7,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates67_valid 6,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates67_valid 5,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 34⟩
  have hMeta : ∀ i, (generatorLeafBlocks15 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks15 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
