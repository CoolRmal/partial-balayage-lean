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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
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

/-- Actual source leaf candidates, block 59 of the recorded finite partition. -/
def generatorLeafBlocks59 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 59 0
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates22 6
    terms := 5
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 59 1
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates22 7
    terms := 5
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 59 2
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates22 6
    terms := 5
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 59 3
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 59 4
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 59 5
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates22 5
    terms := 5
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 59 6
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates22 4
    terms := 5
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 59 7
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates22 5
    terms := 5
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 59 8
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates22 4
    terms := 5
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 59 9
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 59 10
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 59 11
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 59 12
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 59 13
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 59 14
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 59 15
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 59 16
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 59 17
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 59 18
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 59 19
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 59 20
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 59 21
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 59 22
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 59 23
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 59 24
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 59 25
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 59 26
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 59 27
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 59 28
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 59 29
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 59 30
    coordinateU := generatorCoordinates41 5
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 59 31
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 59 32
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 59 33
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 59 34
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 59 35
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 59 36
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 59 37
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 59 38
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 59 39
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates19 4
    terms := 5
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 59 40
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates19 3
    terms := 5
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 59 41
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates19 4
    terms := 5
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 59 42
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates19 3
    terms := 5
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 59 43
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 59 44
    coordinateU := generatorCoordinates42 6
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 59 45
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 59 46
    coordinateU := generatorCoordinates42 5
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 59 47
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 59 48
    coordinateU := generatorCoordinates42 0
    coordinateV := generatorCoordinates18 4
    terms := 12
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 59 49
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates19 0
    terms := 5
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 59 50
    coordinateU := generatorCoordinates43 0
    coordinateV := generatorCoordinates18 7
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 59 51
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates19 0
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 59 52
    coordinateU := generatorCoordinates42 7
    coordinateV := generatorCoordinates18 7
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 59 53
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates18 4
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 59 54
    coordinateU := generatorCoordinates41 7
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 59 55
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 59 56
    coordinateU := generatorCoordinates42 4
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 59 57
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 59 58
    coordinateU := generatorCoordinates42 3
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 59 59
    coordinateU := generatorCoordinates41 6
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 59 60
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 59 61
    coordinateU := generatorCoordinates42 2
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 59 62
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 59 63
    coordinateU := generatorCoordinates42 1
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks59_valid : ∀ i, (generatorLeafBlocks59 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks59 i).coordinateU.IsValid ∧
      (generatorLeafBlocks59 i).coordinateV.IsValid ∧
      (generatorLeafBlocks59 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates41_valid 5,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates42_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates42_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates42_valid 0,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates43_valid 0,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates42_valid 7,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates41_valid 7,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates42_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates42_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates41_valid 6,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates42_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates42_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 2⟩
  have hMeta : ∀ i, (generatorLeafBlocks59 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks59 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
