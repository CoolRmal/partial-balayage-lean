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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates2
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates3
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 96 of the recorded finite partition. -/
def generatorLeafBlocks96 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 96 0
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates6 5
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 96 1
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates6 4
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 96 2
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 96 3
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates6 4
    terms := 0
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 96 4
    coordinateU := generatorCoordinates18 4
    coordinateV := generatorCoordinates5 4
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 96 5
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 96 6
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates6 4
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 96 7
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates6 5
    terms := 0
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 96 8
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates6 4
    terms := 0
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 96 9
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates6 3
    terms := 0
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 96 10
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates6 2
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 96 11
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates6 3
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 96 12
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates6 2
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 96 13
    coordinateU := generatorCoordinates18 4
    coordinateV := generatorCoordinates5 3
    terms := 1
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 96 14
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 96 15
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 16
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 17
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 18
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates6 1
    terms := 0
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 96 19
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 20
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates6 1
    terms := 0
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 21
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates6 0
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 22
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 23
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 24
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 25
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates5 6
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 96 26
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 96 27
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 96 28
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 96 29
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 96 30
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates1 4
    terms := 2
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 96 31
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates1 3
    terms := 2
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 32
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 1 8
  },
  {
    rectangle := generatorPartitionRectangles 96 33
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 34
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 35
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 96 36
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 96 37
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 38
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 39
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 96 40
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 9
  },
  {
    rectangle := generatorPartitionRectangles 96 41
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 42
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates1 6
    terms := 1
    radialRoot := generatorRadialRoots 1 7
  },
  {
    rectangle := generatorPartitionRectangles 96 43
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates1 5
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 44
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 1 6
  },
  {
    rectangle := generatorPartitionRectangles 96 45
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 46
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 47
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 96 48
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 96 49
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 50
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 51
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 96 52
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 1 2
  },
  {
    rectangle := generatorPartitionRectangles 96 53
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 54
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates3 2
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 55
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates3 1
    terms := 1
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 96 56
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 62
  },
  {
    rectangle := generatorPartitionRectangles 96 57
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 96 58
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates3 0
    terms := 1
    radialRoot := generatorRadialRoots 0 61
  },
  {
    rectangle := generatorPartitionRectangles 96 59
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates2 7
    terms := 1
    radialRoot := generatorRadialRoots 0 60
  },
  {
    rectangle := generatorPartitionRectangles 96 60
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 4
  },
  {
    rectangle := generatorPartitionRectangles 96 61
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 62
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates1 2
    terms := 1
    radialRoot := generatorRadialRoots 1 0
  },
  {
    rectangle := generatorPartitionRectangles 96 63
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates1 1
    terms := 0
    radialRoot := generatorRadialRoots 0 61
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks96_valid : ∀ i, (generatorLeafBlocks96 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks96 i).coordinateU.IsValid ∧
      (generatorLeafBlocks96 i).coordinateV.IsValid ∧
      (generatorLeafBlocks96 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates18_valid 4,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates18_valid 4,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates6_valid 1, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates6_valid 0, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates1_valid 4, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates1_valid 3, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 1 8⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 9⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 1 7⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 1 6⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 1 2⟩
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates3_valid 2, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates3_valid 1, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 62⟩
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates3_valid 0, generatorRadialRoots_valid 0 61⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates2_valid 7, generatorRadialRoots_valid 0 60⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 4⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 1 0⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 0 61⟩
  have hMeta : ∀ i, (generatorLeafBlocks96 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks96 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
