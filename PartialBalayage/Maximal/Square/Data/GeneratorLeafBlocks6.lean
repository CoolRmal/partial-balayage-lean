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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates12
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates74
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates76

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 6 of the recorded finite partition. -/
def generatorLeafBlocks6 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 6 0
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates14 2
    terms := 3
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 6 1
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 6 2
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates14 2
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 6 3
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 6 4
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates14 5
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 6 5
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates14 4
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 6
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates14 5
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 7
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates14 4
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 8
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates14 7
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 6 9
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates14 6
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 10
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates14 7
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 11
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates14 6
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 12
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates14 5
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 13
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates14 4
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 14
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates14 5
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 15
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates14 4
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 6 16
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates11 0
    terms := 5
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 6 17
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates10 7
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 6 18
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates11 0
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 6 19
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates10 7
    terms := 12
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 6 20
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates10 6
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 6 21
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates10 5
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 22
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates10 6
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 23
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates10 5
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 24
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates11 0
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 6 25
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates10 7
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 26
    coordinateU := generatorCoordinates76 4
    coordinateV := generatorCoordinates11 0
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 6 27
    coordinateU := generatorCoordinates76 4
    coordinateV := generatorCoordinates10 7
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 28
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates10 6
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 29
    coordinateU := generatorCoordinates77 5
    coordinateV := generatorCoordinates12 0
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 6 30
    coordinateU := generatorCoordinates77 5
    coordinateV := generatorCoordinates11 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 31
    coordinateU := generatorCoordinates77 4
    coordinateV := generatorCoordinates12 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 32
    coordinateU := generatorCoordinates77 4
    coordinateV := generatorCoordinates11 7
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 6 33
    coordinateU := generatorCoordinates77 3
    coordinateV := generatorCoordinates12 2
    terms := 20
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 6 34
    coordinateU := generatorCoordinates77 3
    coordinateV := generatorCoordinates12 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 35
    coordinateU := generatorCoordinates77 2
    coordinateV := generatorCoordinates12 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 36
    coordinateU := generatorCoordinates77 2
    coordinateV := generatorCoordinates12 1
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 6 37
    coordinateU := generatorCoordinates77 3
    coordinateV := generatorCoordinates12 0
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 6 38
    coordinateU := generatorCoordinates77 3
    coordinateV := generatorCoordinates11 7
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 6 39
    coordinateU := generatorCoordinates77 2
    coordinateV := generatorCoordinates12 0
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 6 40
    coordinateU := generatorCoordinates77 2
    coordinateV := generatorCoordinates11 7
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 6 41
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates10 4
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 42
    coordinateU := generatorCoordinates76 7
    coordinateV := generatorCoordinates10 3
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 43
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates10 4
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 44
    coordinateU := generatorCoordinates76 6
    coordinateV := generatorCoordinates10 3
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 6 45
    coordinateU := generatorCoordinates75 7
    coordinateV := generatorCoordinates9 5
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 6 46
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates10 4
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 6 47
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates10 3
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 6 48
    coordinateU := generatorCoordinates77 3
    coordinateV := generatorCoordinates11 6
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 6 49
    coordinateU := generatorCoordinates77 3
    coordinateV := generatorCoordinates11 5
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 6 50
    coordinateU := generatorCoordinates77 2
    coordinateV := generatorCoordinates11 6
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 6 51
    coordinateU := generatorCoordinates77 2
    coordinateV := generatorCoordinates11 5
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 6 52
    coordinateU := generatorCoordinates76 4
    coordinateV := generatorCoordinates10 3
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 6 53
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates10 2
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 6 54
    coordinateU := generatorCoordinates76 5
    coordinateV := generatorCoordinates10 1
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 6 55
    coordinateU := generatorCoordinates76 4
    coordinateV := generatorCoordinates10 2
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 6 56
    coordinateU := generatorCoordinates76 4
    coordinateV := generatorCoordinates10 1
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 6 57
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates11 0
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 6 58
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates10 7
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 59
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates11 0
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 6 60
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates10 7
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 6 61
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates10 6
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 6 62
    coordinateU := generatorCoordinates77 1
    coordinateV := generatorCoordinates12 0
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 6 63
    coordinateU := generatorCoordinates77 1
    coordinateV := generatorCoordinates11 7
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks6_valid : ∀ i, (generatorLeafBlocks6 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks6 i).coordinateU.IsValid ∧
      (generatorLeafBlocks6 i).coordinateV.IsValid ∧
      (generatorLeafBlocks6 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates76_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates77_valid 5,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates77_valid 5,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates77_valid 4,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates77_valid 4,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates77_valid 3,
        generatorCoordinates12_valid 2, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates77_valid 3,
        generatorCoordinates12_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates77_valid 2,
        generatorCoordinates12_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates77_valid 2,
        generatorCoordinates12_valid 1, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates77_valid 3,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates77_valid 3,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates77_valid 2,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates77_valid 2,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates76_valid 7,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates76_valid 6,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates75_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates77_valid 3,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates77_valid 3,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates77_valid 2,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates77_valid 2,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates76_valid 4,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates76_valid 5,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates76_valid 4,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates76_valid 4,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates77_valid 1,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates77_valid 1,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 4 58⟩
  have hMeta : ∀ i, (generatorLeafBlocks6 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks6 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
