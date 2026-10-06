/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 71 of the recorded finite partition. -/
def generatorLeafBlocks71 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 71 0
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 54
  },
  {
    rectangle := generatorPartitionRectangles 71 1
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 71 2
    coordinateU := generatorCoordinates36 2
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 54
  },
  {
    rectangle := generatorPartitionRectangles 71 3
    coordinateU := generatorCoordinates36 2
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 71 4
    coordinateU := generatorCoordinates36 1
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 71 5
    coordinateU := generatorCoordinates36 1
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 52
  },
  {
    rectangle := generatorPartitionRectangles 71 6
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 71 7
    coordinateU := generatorCoordinates33 4
    coordinateV := generatorCoordinates18 5
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 71 8
    coordinateU := generatorCoordinates36 0
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 52
  },
  {
    rectangle := generatorPartitionRectangles 71 9
    coordinateU := generatorCoordinates36 0
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 71 10
    coordinateU := generatorCoordinates35 7
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 71 11
    coordinateU := generatorCoordinates35 7
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 50
  },
  {
    rectangle := generatorPartitionRectangles 71 12
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 71 13
    coordinateU := generatorCoordinates35 6
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 50
  },
  {
    rectangle := generatorPartitionRectangles 71 14
    coordinateU := generatorCoordinates35 6
    coordinateV := generatorCoordinates20 7
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 71 15
    coordinateU := generatorCoordinates35 5
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 71 16
    coordinateU := generatorCoordinates35 5
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 48
  },
  {
    rectangle := generatorPartitionRectangles 71 17
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 71 18
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates18 5
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 71 19
    coordinateU := generatorCoordinates33 4
    coordinateV := generatorCoordinates18 4
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 71 20
    coordinateU := generatorCoordinates33 4
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 71 21
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates18 4
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 71 22
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates18 3
    terms := 5
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 71 23
    coordinateU := generatorCoordinates35 4
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 48
  },
  {
    rectangle := generatorPartitionRectangles 71 24
    coordinateU := generatorCoordinates35 4
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 71 25
    coordinateU := generatorCoordinates35 3
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 71 26
    coordinateU := generatorCoordinates35 3
    coordinateV := generatorCoordinates20 7
    terms := 4
    radialRoot := generatorRadialRoots 2 46
  },
  {
    rectangle := generatorPartitionRectangles 71 27
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 71 28
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 71 29
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 71 30
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates18 5
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 71 31
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates19 6
    terms := 5
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 71 32
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates19 5
    terms := 4
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 71 33
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 2 43
  },
  {
    rectangle := generatorPartitionRectangles 71 34
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 71 35
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 71 36
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates18 4
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 71 37
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates18 3
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 71 38
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates18 4
    terms := 5
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 71 39
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates19 0
    terms := 3
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 71 40
    coordinateU := generatorCoordinates33 6
    coordinateV := generatorCoordinates18 7
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 71 41
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates19 0
    terms := 3
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 71 42
    coordinateU := generatorCoordinates33 5
    coordinateV := generatorCoordinates18 7
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 71 43
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 41
  },
  {
    rectangle := generatorPartitionRectangles 71 44
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 71 45
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 39
  },
  {
    rectangle := generatorPartitionRectangles 71 46
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 71 47
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates15 1
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 71 48
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates15 0
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 71 49
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates15 1
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 71 50
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates15 0
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 71 51
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 37
  },
  {
    rectangle := generatorPartitionRectangles 71 52
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 71 53
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 2 35
  },
  {
    rectangle := generatorPartitionRectangles 71 54
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates15 2
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 71 55
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates14 2
    terms := 5
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 71 56
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates14 7
    terms := 4
    radialRoot := generatorRadialRoots 2 33
  },
  {
    rectangle := generatorPartitionRectangles 71 57
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates14 6
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 71 58
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates14 7
    terms := 4
    radialRoot := generatorRadialRoots 2 31
  },
  {
    rectangle := generatorPartitionRectangles 71 59
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates14 6
    terms := 4
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 71 60
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 29
  },
  {
    rectangle := generatorPartitionRectangles 71 61
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 71 62
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 71 63
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks71_valid : ∀ i, (generatorLeafBlocks71 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks71 i).coordinateU.IsValid ∧
      (generatorLeafBlocks71 i).coordinateV.IsValid ∧
      (generatorLeafBlocks71 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 54⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates36_valid 2,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 54⟩
    · exact ⟨generatorCoordinates36_valid 2,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates36_valid 1,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates36_valid 1,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 52⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates33_valid 4,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates36_valid 0,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 52⟩
    · exact ⟨generatorCoordinates36_valid 0,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates35_valid 7,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates35_valid 7,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 50⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates35_valid 6,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 50⟩
    · exact ⟨generatorCoordinates35_valid 6,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates35_valid 5,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates35_valid 5,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 48⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates33_valid 4,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates33_valid 4,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates35_valid 4,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 48⟩
    · exact ⟨generatorCoordinates35_valid 4,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates35_valid 3,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates35_valid 3,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 46⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 43⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates33_valid 6,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates33_valid 5,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 41⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 39⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 37⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 35⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 33⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 31⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 29⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 25⟩
  have hMeta : ∀ i, (generatorLeafBlocks71 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks71 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
