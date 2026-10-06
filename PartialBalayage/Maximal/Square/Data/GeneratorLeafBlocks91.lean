/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 91 of the recorded finite partition. -/
def generatorLeafBlocks91 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 91 0
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 91 1
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 91 2
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 91 3
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 91 4
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates11 0
    terms := 1
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 91 5
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 91 6
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates11 0
    terms := 1
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 91 7
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 91 8
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 91 9
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 91 10
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 91 11
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 91 12
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 91 13
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates10 3
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 91 14
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 91 15
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates10 3
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 91 16
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 91 17
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates10 1
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 18
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates10 2
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 19
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 20
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 91 21
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates10 3
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 22
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates10 4
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 23
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates10 3
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 24
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates10 2
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 25
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 26
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates10 2
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 27
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 91 28
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 91 29
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 91 30
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 91 31
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 91 32
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 91 33
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 34
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 35
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 36
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 91 37
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 38
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 91 39
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 40
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 41
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 42
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates6 3
    terms := 2
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 43
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates6 2
    terms := 2
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 91 44
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 45
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 46
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 47
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 91 48
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 91 49
    coordinateU := generatorCoordinates23 1
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 91 50
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 91 51
    coordinateU := generatorCoordinates23 0
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 91 52
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates6 1
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 91 53
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 91 54
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates6 1
    terms := 2
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 91 55
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates6 0
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 91 56
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 91 57
    coordinateU := generatorCoordinates22 7
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 91 58
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 91 59
    coordinateU := generatorCoordinates22 6
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 91 60
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates6 5
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 91 61
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 62
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates6 5
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 91 63
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates6 4
    terms := 2
    radialRoot := generatorRadialRoots 1 31
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks91_valid : ∀ i, (generatorLeafBlocks91 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks91 i).coordinateU.IsValid ∧
      (generatorLeafBlocks91 i).coordinateV.IsValid ∧
      (generatorLeafBlocks91 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates23_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates23_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates22_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates22_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 31⟩
  have hMeta : ∀ i, (generatorLeafBlocks91 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks91 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
