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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates27
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates28
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates64
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates66

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 18 of the recorded finite partition. -/
def generatorLeafBlocks18 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 18 0
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 18 1
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates26 5
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 18 2
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates26 4
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 18 3
    coordinateU := generatorCoordinates67 1
    coordinateV := generatorCoordinates28 0
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 18 4
    coordinateU := generatorCoordinates67 1
    coordinateV := generatorCoordinates27 7
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 5
    coordinateU := generatorCoordinates67 0
    coordinateV := generatorCoordinates28 0
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 6
    coordinateU := generatorCoordinates67 0
    coordinateV := generatorCoordinates27 7
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 18 7
    coordinateU := generatorCoordinates66 7
    coordinateV := generatorCoordinates28 2
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 18 8
    coordinateU := generatorCoordinates66 7
    coordinateV := generatorCoordinates28 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 9
    coordinateU := generatorCoordinates66 6
    coordinateV := generatorCoordinates28 2
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 10
    coordinateU := generatorCoordinates66 6
    coordinateV := generatorCoordinates28 1
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 18 11
    coordinateU := generatorCoordinates66 7
    coordinateV := generatorCoordinates28 0
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 18 12
    coordinateU := generatorCoordinates66 7
    coordinateV := generatorCoordinates27 7
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 18 13
    coordinateU := generatorCoordinates66 6
    coordinateV := generatorCoordinates28 0
    terms := 20
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 18 14
    coordinateU := generatorCoordinates66 6
    coordinateV := generatorCoordinates27 7
    terms := 30
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 18 15
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 18 16
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 17
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates26 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 18
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 18 19
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates25 3
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 20
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates26 2
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 18 21
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates26 1
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 22
    coordinateU := generatorCoordinates66 7
    coordinateV := generatorCoordinates27 6
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 18 23
    coordinateU := generatorCoordinates66 7
    coordinateV := generatorCoordinates27 5
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 24
    coordinateU := generatorCoordinates66 6
    coordinateV := generatorCoordinates27 6
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 25
    coordinateU := generatorCoordinates66 6
    coordinateV := generatorCoordinates27 5
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 18 26
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates26 1
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 18 27
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 18 28
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 18 29
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 18 30
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 18 31
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 18 32
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates26 5
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 33
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 18 34
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 18 35
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates26 4
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 18 36
    coordinateU := generatorCoordinates66 5
    coordinateV := generatorCoordinates28 0
    terms := 20
    radialRoot := generatorRadialRoots 4 59
  },
  {
    rectangle := generatorPartitionRectangles 18 37
    coordinateU := generatorCoordinates66 5
    coordinateV := generatorCoordinates27 7
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 38
    coordinateU := generatorCoordinates66 4
    coordinateV := generatorCoordinates28 0
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 39
    coordinateU := generatorCoordinates66 4
    coordinateV := generatorCoordinates27 7
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 18 40
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates26 4
    terms := 20
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 41
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates26 3
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 18 42
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates25 6
    terms := 30
    radialRoot := generatorRadialRoots 4 58
  },
  {
    rectangle := generatorPartitionRectangles 18 43
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 18 44
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 18 45
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates26 4
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 18 46
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates26 3
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 18 47
    coordinateU := generatorCoordinates66 5
    coordinateV := generatorCoordinates27 6
    terms := 30
    radialRoot := generatorRadialRoots 4 56
  },
  {
    rectangle := generatorPartitionRectangles 18 48
    coordinateU := generatorCoordinates66 5
    coordinateV := generatorCoordinates27 5
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 18 49
    coordinateU := generatorCoordinates66 4
    coordinateV := generatorCoordinates27 6
    terms := 30
    radialRoot := generatorRadialRoots 4 54
  },
  {
    rectangle := generatorPartitionRectangles 18 50
    coordinateU := generatorCoordinates66 4
    coordinateV := generatorCoordinates27 5
    terms := 20
    radialRoot := generatorRadialRoots 4 51
  },
  {
    rectangle := generatorPartitionRectangles 18 51
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates26 1
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 18 52
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates26 2
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 18 53
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates26 1
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 18 54
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 18 55
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 18 56
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates26 0
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 18 57
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates25 7
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 18 58
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 18 59
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 18 60
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates26 2
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 18 61
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates26 1
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 18 62
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 18 63
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 4 48
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks18_valid : ∀ i, (generatorLeafBlocks18 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks18 i).coordinateU.IsValid ∧
      (generatorLeafBlocks18 i).coordinateV.IsValid ∧
      (generatorLeafBlocks18 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates67_valid 1,
        generatorCoordinates28_valid 0, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates67_valid 1,
        generatorCoordinates27_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates67_valid 0,
        generatorCoordinates28_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates67_valid 0,
        generatorCoordinates27_valid 7, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates66_valid 7,
        generatorCoordinates28_valid 2, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates66_valid 7,
        generatorCoordinates28_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates66_valid 6,
        generatorCoordinates28_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates66_valid 6,
        generatorCoordinates28_valid 1, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates66_valid 7,
        generatorCoordinates28_valid 0, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates66_valid 7,
        generatorCoordinates27_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates66_valid 6,
        generatorCoordinates28_valid 0, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates66_valid 6,
        generatorCoordinates27_valid 7, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates66_valid 7,
        generatorCoordinates27_valid 6, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates66_valid 7,
        generatorCoordinates27_valid 5, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates66_valid 6,
        generatorCoordinates27_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates66_valid 6,
        generatorCoordinates27_valid 5, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates66_valid 5,
        generatorCoordinates28_valid 0, generatorRadialRoots_valid 4 59⟩
    · exact ⟨generatorCoordinates66_valid 5,
        generatorCoordinates27_valid 7, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates66_valid 4,
        generatorCoordinates28_valid 0, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates66_valid 4,
        generatorCoordinates27_valid 7, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 58⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates66_valid 5,
        generatorCoordinates27_valid 6, generatorRadialRoots_valid 4 56⟩
    · exact ⟨generatorCoordinates66_valid 5,
        generatorCoordinates27_valid 5, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates66_valid 4,
        generatorCoordinates27_valid 6, generatorRadialRoots_valid 4 54⟩
    · exact ⟨generatorCoordinates66_valid 4,
        generatorCoordinates27_valid 5, generatorRadialRoots_valid 4 51⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 48⟩
  have hMeta : ∀ i, (generatorLeafBlocks18 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks18 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
