/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates12
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 94 of the recorded finite partition. -/
def generatorLeafBlocks94 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 94 0
    coordinateU := generatorCoordinates18 1
    coordinateV := generatorCoordinates13 7
    terms := 0
    radialRoot := generatorRadialRoots 1 43
  },
  {
    rectangle := generatorPartitionRectangles 94 1
    coordinateU := generatorCoordinates18 4
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 94 2
    coordinateU := generatorCoordinates18 4
    coordinateV := generatorCoordinates14 0
    terms := 0
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 94 3
    coordinateU := generatorCoordinates18 3
    coordinateV := generatorCoordinates14 1
    terms := 0
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 94 4
    coordinateU := generatorCoordinates18 3
    coordinateV := generatorCoordinates14 0
    terms := 0
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 5
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates11 0
    terms := 0
    radialRoot := generatorRadialRoots 1 42
  },
  {
    rectangle := generatorPartitionRectangles 94 6
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates10 7
    terms := 1
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 94 7
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates11 0
    terms := 0
    radialRoot := generatorRadialRoots 1 41
  },
  {
    rectangle := generatorPartitionRectangles 94 8
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates10 7
    terms := 0
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 94 9
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 94 10
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates12 0
    terms := 1
    radialRoot := generatorRadialRoots 1 39
  },
  {
    rectangle := generatorPartitionRectangles 94 11
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates11 7
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 94 12
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates12 0
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 94 13
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates11 7
    terms := 1
    radialRoot := generatorRadialRoots 1 37
  },
  {
    rectangle := generatorPartitionRectangles 94 14
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 94 15
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates10 5
    terms := 2
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 94 16
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates11 0
    terms := 0
    radialRoot := generatorRadialRoots 1 40
  },
  {
    rectangle := generatorPartitionRectangles 94 17
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates10 7
    terms := 0
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 94 18
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates11 0
    terms := 0
    radialRoot := generatorRadialRoots 1 38
  },
  {
    rectangle := generatorPartitionRectangles 94 19
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates10 7
    terms := 0
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 94 20
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates10 6
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 94 21
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates12 0
    terms := 1
    radialRoot := generatorRadialRoots 1 35
  },
  {
    rectangle := generatorPartitionRectangles 94 22
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates11 7
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 23
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates12 0
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 24
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates11 7
    terms := 1
    radialRoot := generatorRadialRoots 1 33
  },
  {
    rectangle := generatorPartitionRectangles 94 25
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates10 6
    terms := 0
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 26
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates10 5
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 27
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates11 6
    terms := 1
    radialRoot := generatorRadialRoots 1 37
  },
  {
    rectangle := generatorPartitionRectangles 94 28
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates11 5
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 94 29
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates11 6
    terms := 1
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 94 30
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates11 5
    terms := 1
    radialRoot := generatorRadialRoots 1 35
  },
  {
    rectangle := generatorPartitionRectangles 94 31
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates11 4
    terms := 1
    radialRoot := generatorRadialRoots 1 35
  },
  {
    rectangle := generatorPartitionRectangles 94 32
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates11 3
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 33
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates11 4
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 34
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates11 3
    terms := 1
    radialRoot := generatorRadialRoots 1 33
  },
  {
    rectangle := generatorPartitionRectangles 94 35
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates11 6
    terms := 1
    radialRoot := generatorRadialRoots 1 35
  },
  {
    rectangle := generatorPartitionRectangles 94 36
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates11 5
    terms := 2
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 37
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates11 6
    terms := 1
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 94 38
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates11 5
    terms := 2
    radialRoot := generatorRadialRoots 1 33
  },
  {
    rectangle := generatorPartitionRectangles 94 39
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates11 4
    terms := 2
    radialRoot := generatorRadialRoots 1 33
  },
  {
    rectangle := generatorPartitionRectangles 94 40
    coordinateU := generatorCoordinates20 6
    coordinateV := generatorCoordinates11 3
    terms := 2
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 41
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates11 4
    terms := 3
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 42
    coordinateU := generatorCoordinates20 5
    coordinateV := generatorCoordinates11 3
    terms := 2
    radialRoot := generatorRadialRoots 1 29
  },
  {
    rectangle := generatorPartitionRectangles 94 43
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates11 2
    terms := 1
    radialRoot := generatorRadialRoots 1 33
  },
  {
    rectangle := generatorPartitionRectangles 94 44
    coordinateU := generatorCoordinates21 0
    coordinateV := generatorCoordinates11 1
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 45
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates11 2
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 46
    coordinateU := generatorCoordinates20 7
    coordinateV := generatorCoordinates11 1
    terms := 1
    radialRoot := generatorRadialRoots 1 29
  },
  {
    rectangle := generatorPartitionRectangles 94 47
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 94 48
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates10 2
    terms := 3
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 94 49
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 94 50
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates11 6
    terms := 2
    radialRoot := generatorRadialRoots 1 33
  },
  {
    rectangle := generatorPartitionRectangles 94 51
    coordinateU := generatorCoordinates21 2
    coordinateV := generatorCoordinates13 2
    terms := 2
    radialRoot := generatorRadialRoots 1 32
  },
  {
    rectangle := generatorPartitionRectangles 94 52
    coordinateU := generatorCoordinates21 2
    coordinateV := generatorCoordinates13 1
    terms := 2
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 53
    coordinateU := generatorCoordinates21 1
    coordinateV := generatorCoordinates13 2
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 54
    coordinateU := generatorCoordinates21 1
    coordinateV := generatorCoordinates13 1
    terms := 1
    radialRoot := generatorRadialRoots 1 30
  },
  {
    rectangle := generatorPartitionRectangles 94 55
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates11 6
    terms := 1
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 94 56
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates11 5
    terms := 2
    radialRoot := generatorRadialRoots 1 29
  },
  {
    rectangle := generatorPartitionRectangles 94 57
    coordinateU := generatorCoordinates21 2
    coordinateV := generatorCoordinates13 0
    terms := 2
    radialRoot := generatorRadialRoots 1 30
  },
  {
    rectangle := generatorPartitionRectangles 94 58
    coordinateU := generatorCoordinates21 2
    coordinateV := generatorCoordinates12 7
    terms := 2
    radialRoot := generatorRadialRoots 1 29
  },
  {
    rectangle := generatorPartitionRectangles 94 59
    coordinateU := generatorCoordinates21 1
    coordinateV := generatorCoordinates13 0
    terms := 2
    radialRoot := generatorRadialRoots 1 29
  },
  {
    rectangle := generatorPartitionRectangles 94 60
    coordinateU := generatorCoordinates21 1
    coordinateV := generatorCoordinates12 7
    terms := 2
    radialRoot := generatorRadialRoots 1 28
  },
  {
    rectangle := generatorPartitionRectangles 94 61
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates11 3
    terms := 3
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 94 62
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates11 4
    terms := 2
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 94 63
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates11 3
    terms := 2
    radialRoot := generatorRadialRoots 1 26
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks94_valid : ∀ i, (generatorLeafBlocks94 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks94 i).coordinateU.IsValid ∧
      (generatorLeafBlocks94 i).coordinateV.IsValid ∧
      (generatorLeafBlocks94 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates18_valid 1,
        generatorCoordinates13_valid 7, generatorRadialRoots_valid 1 43⟩
    · exact ⟨generatorCoordinates18_valid 4,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates18_valid 4,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates18_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates18_valid 3,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 42⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 41⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 1 39⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 1 37⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 40⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 38⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 1 35⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates12_valid 0, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates11_valid 7, generatorRadialRoots_valid 1 33⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 37⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 1 35⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates11_valid 4, generatorRadialRoots_valid 1 35⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates11_valid 4, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 33⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 35⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 1 33⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates11_valid 4, generatorRadialRoots_valid 1 33⟩
    · exact ⟨generatorCoordinates20_valid 6,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates11_valid 4, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates20_valid 5,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 29⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates11_valid 2, generatorRadialRoots_valid 1 33⟩
    · exact ⟨generatorCoordinates21_valid 0,
        generatorCoordinates11_valid 1, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates11_valid 2, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates20_valid 7,
        generatorCoordinates11_valid 1, generatorRadialRoots_valid 1 29⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 33⟩
    · exact ⟨generatorCoordinates21_valid 2,
        generatorCoordinates13_valid 2, generatorRadialRoots_valid 1 32⟩
    · exact ⟨generatorCoordinates21_valid 2,
        generatorCoordinates13_valid 1, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates21_valid 1,
        generatorCoordinates13_valid 2, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates21_valid 1,
        generatorCoordinates13_valid 1, generatorRadialRoots_valid 1 30⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 1 29⟩
    · exact ⟨generatorCoordinates21_valid 2,
        generatorCoordinates13_valid 0, generatorRadialRoots_valid 1 30⟩
    · exact ⟨generatorCoordinates21_valid 2,
        generatorCoordinates12_valid 7, generatorRadialRoots_valid 1 29⟩
    · exact ⟨generatorCoordinates21_valid 1,
        generatorCoordinates13_valid 0, generatorRadialRoots_valid 1 29⟩
    · exact ⟨generatorCoordinates21_valid 1,
        generatorCoordinates12_valid 7, generatorRadialRoots_valid 1 28⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates11_valid 4, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 26⟩
  have hMeta : ∀ i, (generatorLeafBlocks94 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks94 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
