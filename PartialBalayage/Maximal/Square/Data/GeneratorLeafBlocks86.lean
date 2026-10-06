/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates1
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 86 of the recorded finite partition. -/
def generatorLeafBlocks86 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 86 0
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 86 1
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 86 2
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 86 3
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 86 4
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 86 5
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 86 6
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 86 7
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates6 1
    terms := 2
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 86 8
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 86 9
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates6 1
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 86 10
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 86 11
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 86 12
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 86 13
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 86 14
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 86 15
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates5 3
    terms := 3
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 86 16
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 86 17
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 86 18
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 86 19
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 86 20
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates6 5
    terms := 3
    radialRoot := generatorRadialRoots 1 46
  },
  {
    rectangle := generatorPartitionRectangles 86 21
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates6 4
    terms := 3
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 86 22
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 86 23
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 86 24
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates6 3
    terms := 3
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 86 25
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 86 26
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 86 27
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 86 28
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 86 29
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 86 30
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 86 31
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 86 32
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 86 33
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 86 34
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 86 35
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 86 36
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates5 3
    terms := 4
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 86 37
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 86 38
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 39
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 40
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 86 41
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 86 42
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 43
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 44
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 86 45
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 86 46
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 86 47
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 86 48
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 86 49
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 86 50
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 86 51
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 86 52
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 86 53
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 86 54
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 55
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 56
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 86 57
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 86 58
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 59
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates1 6
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 86 60
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates1 5
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 86 61
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 86 62
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 86 63
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 34
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks86_valid : ∀ i, (generatorLeafBlocks86 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks86 i).coordinateU.IsValid ∧
      (generatorLeafBlocks86 i).coordinateV.IsValid ∧
      (generatorLeafBlocks86 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 46⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 34⟩
  have hMeta : ∀ i, (generatorLeafBlocks86 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks86 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
