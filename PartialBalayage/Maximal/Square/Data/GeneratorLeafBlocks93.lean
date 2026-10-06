/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates0
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates1
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates2
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates3
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
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

/-- Actual source leaf candidates, block 93 of the recorded finite partition. -/
def generatorLeafBlocks93 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 93 0
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 93 1
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 93 2
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 93 3
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 93 4
    coordinateU := generatorCoordinates23 7
    coordinateV := generatorCoordinates3 0
    terms := 2
    radialRoot := generatorRadialRoots 1 16
  },
  {
    rectangle := generatorPartitionRectangles 93 5
    coordinateU := generatorCoordinates23 7
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 93 6
    coordinateU := generatorCoordinates23 6
    coordinateV := generatorCoordinates3 0
    terms := 2
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 93 7
    coordinateU := generatorCoordinates23 6
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 14
  },
  {
    rectangle := generatorPartitionRectangles 93 8
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates1 4
    terms := 3
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 93 9
    coordinateU := generatorCoordinates23 5
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 1 14
  },
  {
    rectangle := generatorPartitionRectangles 93 10
    coordinateU := generatorCoordinates23 5
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 93 11
    coordinateU := generatorCoordinates23 4
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 93 12
    coordinateU := generatorCoordinates23 4
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 12
  },
  {
    rectangle := generatorPartitionRectangles 93 13
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 93 14
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 93 15
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 93 16
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 93 17
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 93 18
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates1 3
    terms := 3
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 93 19
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 93 20
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 93 21
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 93 22
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 93 23
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 93 24
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 93 25
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 93 26
    coordinateU := generatorCoordinates22 5
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 93 27
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 93 28
    coordinateU := generatorCoordinates22 4
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 93 29
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 93 30
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 93 31
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 93 32
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates1 1
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 93 33
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 93 34
    coordinateU := generatorCoordinates22 3
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 93 35
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates1 0
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 93 36
    coordinateU := generatorCoordinates22 2
    coordinateV := generatorCoordinates0 7
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 93 37
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates19 6
    terms := 0
    radialRoot := generatorRadialRoots 2 4
  },
  {
    rectangle := generatorPartitionRectangles 93 38
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates19 5
    terms := 0
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 93 39
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates19 6
    terms := 0
    radialRoot := generatorRadialRoots 2 3
  },
  {
    rectangle := generatorPartitionRectangles 93 40
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates19 5
    terms := 0
    radialRoot := generatorRadialRoots 2 1
  },
  {
    rectangle := generatorPartitionRectangles 93 41
    coordinateU := generatorCoordinates18 6
    coordinateV := generatorCoordinates18 5
    terms := 0
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 93 42
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates18 6
    terms := 0
    radialRoot := generatorRadialRoots 1 63
  },
  {
    rectangle := generatorPartitionRectangles 93 43
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates18 5
    terms := 0
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 93 44
    coordinateU := generatorCoordinates18 6
    coordinateV := generatorCoordinates18 4
    terms := 0
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 93 45
    coordinateU := generatorCoordinates18 6
    coordinateV := generatorCoordinates18 3
    terms := 0
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 93 46
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates18 4
    terms := 0
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 93 47
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates18 3
    terms := 0
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 93 48
    coordinateU := generatorCoordinates18 4
    coordinateV := generatorCoordinates18 6
    terms := 0
    radialRoot := generatorRadialRoots 1 59
  },
  {
    rectangle := generatorPartitionRectangles 93 49
    coordinateU := generatorCoordinates18 4
    coordinateV := generatorCoordinates18 5
    terms := 0
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 93 50
    coordinateU := generatorCoordinates18 3
    coordinateV := generatorCoordinates18 6
    terms := 0
    radialRoot := generatorRadialRoots 1 55
  },
  {
    rectangle := generatorPartitionRectangles 93 51
    coordinateU := generatorCoordinates18 3
    coordinateV := generatorCoordinates18 5
    terms := 0
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 93 52
    coordinateU := generatorCoordinates18 1
    coordinateV := generatorCoordinates18 1
    terms := 0
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 93 53
    coordinateU := generatorCoordinates18 6
    coordinateV := generatorCoordinates14 3
    terms := 0
    radialRoot := generatorRadialRoots 1 51
  },
  {
    rectangle := generatorPartitionRectangles 93 54
    coordinateU := generatorCoordinates18 6
    coordinateV := generatorCoordinates14 2
    terms := 0
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 93 55
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates14 3
    terms := 0
    radialRoot := generatorRadialRoots 1 47
  },
  {
    rectangle := generatorPartitionRectangles 93 56
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates14 2
    terms := 0
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 93 57
    coordinateU := generatorCoordinates18 6
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 1 45
  },
  {
    rectangle := generatorPartitionRectangles 93 58
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates14 5
    terms := 0
    radialRoot := generatorRadialRoots 1 44
  },
  {
    rectangle := generatorPartitionRectangles 93 59
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates14 4
    terms := 0
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 93 60
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates14 5
    terms := 0
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 93 61
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates14 4
    terms := 0
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 93 62
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 93 63
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates14 0
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks93_valid : ∀ i, (generatorLeafBlocks93 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks93 i).coordinateU.IsValid ∧
      (generatorLeafBlocks93 i).coordinateV.IsValid ∧
      (generatorLeafBlocks93 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates23_valid 7,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 16⟩
    · exact ⟨generatorCoordinates23_valid 7,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates23_valid 6,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates23_valid 6,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 14⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates23_valid 5,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 14⟩
    · exact ⟨generatorCoordinates23_valid 5,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates23_valid 4,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates23_valid 4,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 12⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates22_valid 5,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates22_valid 4,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates22_valid 3,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates1_valid 0, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates22_valid 2,
        generatorCoordinates0_valid 7, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 4⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 3⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 1⟩
    · exact ⟨generatorCoordinates18_valid 6,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 1 63⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates18_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates18_valid 6,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates18_valid 4,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 1 59⟩
    · exact ⟨generatorCoordinates18_valid 4,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates18_valid 3,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 1 55⟩
    · exact ⟨generatorCoordinates18_valid 3,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates18_valid 1,
        generatorCoordinates18_valid 1, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates18_valid 6,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 1 51⟩
    · exact ⟨generatorCoordinates18_valid 6,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 1 47⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates18_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 1 45⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 44⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 1 41⟩
  have hMeta : ∀ i, (generatorLeafBlocks93 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks93 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
