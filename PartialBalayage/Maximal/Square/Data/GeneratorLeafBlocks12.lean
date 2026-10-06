/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates70
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates72

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 12 of the recorded finite partition. -/
def generatorLeafBlocks12 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 12 0
    coordinateU := generatorCoordinates72 0
    coordinateV := generatorCoordinates20 2
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 12 1
    coordinateU := generatorCoordinates72 0
    coordinateV := generatorCoordinates20 1
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 12 2
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates19 2
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 12 3
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates19 1
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 12 4
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates19 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 12 5
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates19 1
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 12 6
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates19 0
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 12 7
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates18 7
    terms := 8
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 8
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates19 0
    terms := 12
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 9
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates18 7
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 12 10
    coordinateU := generatorCoordinates72 3
    coordinateV := generatorCoordinates20 0
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 12 11
    coordinateU := generatorCoordinates72 3
    coordinateV := generatorCoordinates19 7
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 12 12
    coordinateU := generatorCoordinates72 2
    coordinateV := generatorCoordinates20 0
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 12 13
    coordinateU := generatorCoordinates72 2
    coordinateV := generatorCoordinates19 7
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 12 14
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates19 1
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 15
    coordinateU := generatorCoordinates72 1
    coordinateV := generatorCoordinates20 0
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 12 16
    coordinateU := generatorCoordinates72 1
    coordinateV := generatorCoordinates19 7
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 17
    coordinateU := generatorCoordinates72 0
    coordinateV := generatorCoordinates20 0
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 18
    coordinateU := generatorCoordinates72 0
    coordinateV := generatorCoordinates19 7
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 12 19
    coordinateU := generatorCoordinates71 2
    coordinateV := generatorCoordinates19 1
    terms := 50
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 12 20
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates19 0
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 12 21
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates18 7
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 12 22
    coordinateU := generatorCoordinates71 2
    coordinateV := generatorCoordinates19 0
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 12 23
    coordinateU := generatorCoordinates71 2
    coordinateV := generatorCoordinates18 7
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 12 24
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 12 25
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 12 26
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 12 27
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 12 28
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates19 4
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 12 29
    coordinateU := generatorCoordinates71 7
    coordinateV := generatorCoordinates20 2
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 12 30
    coordinateU := generatorCoordinates71 7
    coordinateV := generatorCoordinates20 1
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 31
    coordinateU := generatorCoordinates71 6
    coordinateV := generatorCoordinates20 2
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 32
    coordinateU := generatorCoordinates71 6
    coordinateV := generatorCoordinates20 1
    terms := 20
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 12 33
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates19 4
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 34
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates19 3
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 12 35
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates18 6
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 12 36
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates19 4
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 12 37
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates19 3
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 12 38
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates19 4
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 12 39
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates19 3
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 12 40
    coordinateU := generatorCoordinates71 7
    coordinateV := generatorCoordinates20 0
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 12 41
    coordinateU := generatorCoordinates71 7
    coordinateV := generatorCoordinates19 7
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 12 42
    coordinateU := generatorCoordinates71 6
    coordinateV := generatorCoordinates20 0
    terms := 20
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 12 43
    coordinateU := generatorCoordinates71 6
    coordinateV := generatorCoordinates19 7
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 12 44
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates19 1
    terms := 30
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 12 45
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates19 2
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 12 46
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates19 1
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 12 47
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates19 0
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 12 48
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates18 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 12 49
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates19 0
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 12 50
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates18 7
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 12 51
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates19 2
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 12 52
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates19 1
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 12 53
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates19 2
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 12 54
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates19 1
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 12 55
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 12 56
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 12 57
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 12 58
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 12 59
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 12 60
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 12 61
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates14 0
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 12 62
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 12 63
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks12_valid : ∀ i, (generatorLeafBlocks12 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks12 i).coordinateU.IsValid ∧
      (generatorLeafBlocks12 i).coordinateV.IsValid ∧
      (generatorLeafBlocks12 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates72_valid 0,
        generatorCoordinates20_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates72_valid 0,
        generatorCoordinates20_valid 1, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates72_valid 3,
        generatorCoordinates20_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates72_valid 3,
        generatorCoordinates19_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates72_valid 2,
        generatorCoordinates20_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates72_valid 2,
        generatorCoordinates19_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates72_valid 1,
        generatorCoordinates20_valid 0, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates72_valid 1,
        generatorCoordinates19_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates72_valid 0,
        generatorCoordinates20_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates72_valid 0,
        generatorCoordinates19_valid 7, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates71_valid 2,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates71_valid 2,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates71_valid 2,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates71_valid 7,
        generatorCoordinates20_valid 2, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates71_valid 7,
        generatorCoordinates20_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates71_valid 6,
        generatorCoordinates20_valid 2, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates71_valid 6,
        generatorCoordinates20_valid 1, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates71_valid 7,
        generatorCoordinates20_valid 0, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates71_valid 7,
        generatorCoordinates19_valid 7, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates71_valid 6,
        generatorCoordinates20_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates71_valid 6,
        generatorCoordinates19_valid 7, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 4 30⟩
  have hMeta : ∀ i, (generatorLeafBlocks12 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks12 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
