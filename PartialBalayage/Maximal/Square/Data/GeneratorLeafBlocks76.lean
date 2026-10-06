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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 76 of the recorded finite partition. -/
def generatorLeafBlocks76 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 76 0
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates22 7
    terms := 3
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 76 1
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates22 6
    terms := 3
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 76 2
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates21 7
    terms := 3
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 76 3
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 76 4
    coordinateU := generatorCoordinates31 5
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 36
  },
  {
    rectangle := generatorPartitionRectangles 76 5
    coordinateU := generatorCoordinates31 5
    coordinateV := generatorCoordinates23 2
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 6
    coordinateU := generatorCoordinates31 4
    coordinateV := generatorCoordinates23 3
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 7
    coordinateU := generatorCoordinates31 4
    coordinateV := generatorCoordinates23 2
    terms := 4
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 76 8
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 9
    coordinateU := generatorCoordinates31 3
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 76 10
    coordinateU := generatorCoordinates31 3
    coordinateV := generatorCoordinates23 2
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 76 11
    coordinateU := generatorCoordinates31 2
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 76 12
    coordinateU := generatorCoordinates31 2
    coordinateV := generatorCoordinates23 2
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 76 13
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates22 5
    terms := 3
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 76 14
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates22 4
    terms := 3
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 15
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates22 5
    terms := 3
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 16
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates22 4
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 76 17
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 76 18
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 76 19
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates22 3
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 76 20
    coordinateU := generatorCoordinates30 7
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 30
  },
  {
    rectangle := generatorPartitionRectangles 76 21
    coordinateU := generatorCoordinates30 7
    coordinateV := generatorCoordinates23 2
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 76 22
    coordinateU := generatorCoordinates30 6
    coordinateV := generatorCoordinates23 3
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 76 23
    coordinateU := generatorCoordinates30 6
    coordinateV := generatorCoordinates23 2
    terms := 3
    radialRoot := generatorRadialRoots 2 28
  },
  {
    rectangle := generatorPartitionRectangles 76 24
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 76 25
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 76 26
    coordinateU := generatorCoordinates32 3
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 40
  },
  {
    rectangle := generatorPartitionRectangles 76 27
    coordinateU := generatorCoordinates32 3
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 76 28
    coordinateU := generatorCoordinates32 2
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 76 29
    coordinateU := generatorCoordinates32 2
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 38
  },
  {
    rectangle := generatorPartitionRectangles 76 30
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 76 31
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 32
    coordinateU := generatorCoordinates32 1
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 38
  },
  {
    rectangle := generatorPartitionRectangles 76 33
    coordinateU := generatorCoordinates32 1
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 76 34
    coordinateU := generatorCoordinates32 0
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 76 35
    coordinateU := generatorCoordinates32 0
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 36
  },
  {
    rectangle := generatorPartitionRectangles 76 36
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 37
    coordinateU := generatorCoordinates31 7
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 36
  },
  {
    rectangle := generatorPartitionRectangles 76 38
    coordinateU := generatorCoordinates31 7
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 39
    coordinateU := generatorCoordinates31 6
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 76 40
    coordinateU := generatorCoordinates31 6
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 76 41
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 76 42
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates18 5
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 76 43
    coordinateU := generatorCoordinates29 5
    coordinateV := generatorCoordinates18 4
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 76 44
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates19 0
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 76 45
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates18 7
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 76 46
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates19 0
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 76 47
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates18 7
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 76 48
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates18 4
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 76 49
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 76 50
    coordinateU := generatorCoordinates31 5
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 34
  },
  {
    rectangle := generatorPartitionRectangles 76 51
    coordinateU := generatorCoordinates31 5
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 76 52
    coordinateU := generatorCoordinates31 4
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 76 53
    coordinateU := generatorCoordinates31 4
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 76 54
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 76 55
    coordinateU := generatorCoordinates31 3
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 32
  },
  {
    rectangle := generatorPartitionRectangles 76 56
    coordinateU := generatorCoordinates31 3
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 76 57
    coordinateU := generatorCoordinates31 2
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 76 58
    coordinateU := generatorCoordinates31 2
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 30
  },
  {
    rectangle := generatorPartitionRectangles 76 59
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 76 60
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates18 5
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 76 61
    coordinateU := generatorCoordinates31 1
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 30
  },
  {
    rectangle := generatorPartitionRectangles 76 62
    coordinateU := generatorCoordinates31 1
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 76 63
    coordinateU := generatorCoordinates31 0
    coordinateV := generatorCoordinates21 0
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks76_valid : ∀ i, (generatorLeafBlocks76 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks76 i).coordinateU.IsValid ∧
      (generatorLeafBlocks76 i).coordinateV.IsValid ∧
      (generatorLeafBlocks76 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates31_valid 5,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 36⟩
    · exact ⟨generatorCoordinates31_valid 5,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates31_valid 4,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates31_valid 4,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates31_valid 3,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates31_valid 3,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates31_valid 2,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates31_valid 2,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates30_valid 7,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 30⟩
    · exact ⟨generatorCoordinates30_valid 7,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates30_valid 6,
        generatorCoordinates23_valid 3, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates30_valid 6,
        generatorCoordinates23_valid 2, generatorRadialRoots_valid 2 28⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates32_valid 3,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 40⟩
    · exact ⟨generatorCoordinates32_valid 3,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates32_valid 2,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates32_valid 2,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 38⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates32_valid 1,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 38⟩
    · exact ⟨generatorCoordinates32_valid 1,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates32_valid 0,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates32_valid 0,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 36⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates31_valid 7,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 36⟩
    · exact ⟨generatorCoordinates31_valid 7,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates31_valid 6,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates31_valid 6,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates29_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates31_valid 5,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 34⟩
    · exact ⟨generatorCoordinates31_valid 5,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates31_valid 4,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates31_valid 4,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates31_valid 3,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 32⟩
    · exact ⟨generatorCoordinates31_valid 3,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates31_valid 2,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates31_valid 2,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 30⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates31_valid 1,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 30⟩
    · exact ⟨generatorCoordinates31_valid 1,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates31_valid 0,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 29⟩
  have hMeta : ∀ i, (generatorLeafBlocks76 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks76 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
