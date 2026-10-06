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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
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

/-- Actual source leaf candidates, block 19 of the recorded finite partition. -/
def generatorLeafBlocks19 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 19 0
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 19 1
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 19 2
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 19 3
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 19 4
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates21 6
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 19 5
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 19 6
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates21 6
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 19 7
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 19 8
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 19 9
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates22 1
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 19 10
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates22 0
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 19 11
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 19 12
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 19 13
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 19 14
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 19 15
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates22 2
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 19 16
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates21 7
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 19 17
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 19 18
    coordinateU := generatorCoordinates65 5
    coordinateV := generatorCoordinates22 2
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 19 19
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 19 20
    coordinateU := generatorCoordinates65 4
    coordinateV := generatorCoordinates22 2
    terms := 20
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 19 21
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 19 22
    coordinateU := generatorCoordinates66 3
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 19 23
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 19 24
    coordinateU := generatorCoordinates66 2
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 19 25
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates18 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 19 26
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 19 27
    coordinateU := generatorCoordinates66 1
    coordinateV := generatorCoordinates19 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 19 28
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates19 6
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 19 29
    coordinateU := generatorCoordinates66 0
    coordinateV := generatorCoordinates19 5
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 19 30
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates18 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 19 31
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates18 4
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 19 32
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 19 33
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates18 4
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 19 34
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 19 35
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates19 6
    terms := 20
    radialRoot := generatorRadialRoots 4 24
  },
  {
    rectangle := generatorPartitionRectangles 19 36
    coordinateU := generatorCoordinates65 7
    coordinateV := generatorCoordinates19 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 19 37
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates19 6
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 19 38
    coordinateU := generatorCoordinates65 6
    coordinateV := generatorCoordinates19 5
    terms := 20
    radialRoot := generatorRadialRoots 4 20
  },
  {
    rectangle := generatorPartitionRectangles 19 39
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates18 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 19 40
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates18 6
    terms := 30
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 19 41
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates18 5
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 19 42
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates18 4
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 19 43
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 19 44
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates18 4
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 19 45
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 19 46
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 19 47
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 19 48
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 19 49
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 19 50
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 19 51
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 19 52
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 19 53
    coordinateU := generatorCoordinates65 2
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 19 54
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 19 55
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 19 56
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates14 3
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 19 57
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates14 2
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 19 58
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 19 59
    coordinateU := generatorCoordinates65 1
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 19 60
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates14 1
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  },
  {
    rectangle := generatorPartitionRectangles 19 61
    coordinateU := generatorCoordinates65 0
    coordinateV := generatorCoordinates14 0
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 19 62
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates10 0
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 19 63
    coordinateU := generatorCoordinates65 3
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks19_valid : ∀ i, (generatorLeafBlocks19 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks19 i).coordinateU.IsValid ∧
      (generatorLeafBlocks19 i).coordinateV.IsValid ∧
      (generatorLeafBlocks19 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates65_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates65_valid 4,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates66_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates66_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates66_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates66_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 24⟩
    · exact ⟨generatorCoordinates65_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates65_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 4 20⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates65_valid 2,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates65_valid 1,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 54⟩
    · exact ⟨generatorCoordinates65_valid 0,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates65_valid 3,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 3 54⟩
  have hMeta : ∀ i, (generatorLeafBlocks19 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks19 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
