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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 77 of the recorded finite partition. -/
def generatorLeafBlocks77 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 77 0
    coordinateU := generatorCoordinates31 0
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 28
  },
  {
    rectangle := generatorPartitionRectangles 77 1
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 77 2
    coordinateU := generatorCoordinates30 7
    coordinateV := generatorCoordinates21 0
    terms := 3
    radialRoot := generatorRadialRoots 2 28
  },
  {
    rectangle := generatorPartitionRectangles 77 3
    coordinateU := generatorCoordinates30 7
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 77 4
    coordinateU := generatorCoordinates30 6
    coordinateV := generatorCoordinates21 0
    terms := 3
    radialRoot := generatorRadialRoots 2 27
  },
  {
    rectangle := generatorPartitionRectangles 77 5
    coordinateU := generatorCoordinates30 6
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 26
  },
  {
    rectangle := generatorPartitionRectangles 77 6
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 77 7
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates19 4
    terms := 2
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 77 8
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates19 3
    terms := 2
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 77 9
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates19 4
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 77 10
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates19 3
    terms := 2
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 77 11
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates18 4
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 77 12
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 77 13
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates18 7
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 14
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 15
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 77 16
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates19 2
    terms := 2
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 77 17
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates19 1
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 18
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates19 2
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 19
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates19 1
    terms := 2
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 77 20
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 77 21
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 77 22
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 77 23
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 77 24
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 25
  },
  {
    rectangle := generatorPartitionRectangles 77 25
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 77 26
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 23
  },
  {
    rectangle := generatorPartitionRectangles 77 27
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 77 28
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 77 29
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 30
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 31
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 77 32
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 77 33
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 34
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 77 35
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 77 36
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates14 2
    terms := 5
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 77 37
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 77 38
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 77 39
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates14 7
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 77 40
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates14 6
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 77 41
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 77 42
    coordinateU := generatorCoordinates30 5
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 77 43
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 77 44
    coordinateU := generatorCoordinates30 4
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 77 45
    coordinateU := generatorCoordinates29 4
    coordinateV := generatorCoordinates14 1
    terms := 5
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 77 46
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 77 47
    coordinateU := generatorCoordinates30 3
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 77 48
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates14 5
    terms := 3
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 77 49
    coordinateU := generatorCoordinates30 2
    coordinateV := generatorCoordinates14 4
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 77 50
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 77 51
    coordinateU := generatorCoordinates30 1
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 77 52
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates15 3
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 77 53
    coordinateU := generatorCoordinates30 0
    coordinateV := generatorCoordinates15 2
    terms := 3
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 77 54
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 77 55
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 77 56
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 77 57
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 77 58
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 77 59
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates15 1
    terms := 2
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 77 60
    coordinateU := generatorCoordinates29 7
    coordinateV := generatorCoordinates15 0
    terms := 2
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 77 61
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates15 1
    terms := 2
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 77 62
    coordinateU := generatorCoordinates29 6
    coordinateV := generatorCoordinates15 0
    terms := 2
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 77 63
    coordinateU := generatorCoordinates29 3
    coordinateV := generatorCoordinates14 1
    terms := 5
    radialRoot := generatorRadialRoots 2 11
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks77_valid : ∀ i, (generatorLeafBlocks77 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks77 i).coordinateU.IsValid ∧
      (generatorLeafBlocks77 i).coordinateV.IsValid ∧
      (generatorLeafBlocks77 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates31_valid 0,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 28⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates30_valid 7,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 28⟩
    · exact ⟨generatorCoordinates30_valid 7,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates30_valid 6,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 27⟩
    · exact ⟨generatorCoordinates30_valid 6,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 26⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 25⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 23⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates30_valid 5,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates30_valid 4,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates29_valid 4,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates30_valid 3,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates30_valid 2,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates30_valid 1,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates30_valid 0,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates29_valid 7,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates29_valid 6,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates29_valid 3,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 2 11⟩
  have hMeta : ∀ i, (generatorLeafBlocks77 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks77 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
