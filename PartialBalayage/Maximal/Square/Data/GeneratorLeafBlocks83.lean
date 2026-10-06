/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates27
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates28

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 83 of the recorded finite partition. -/
def generatorLeafBlocks83 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 83 0
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 83 1
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates19 4
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 83 2
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates19 3
    terms := 2
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 83 3
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates19 4
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 83 4
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates19 3
    terms := 2
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 83 5
    coordinateU := generatorCoordinates28 2
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 22
  },
  {
    rectangle := generatorPartitionRectangles 83 6
    coordinateU := generatorCoordinates28 2
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 83 7
    coordinateU := generatorCoordinates28 1
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 21
  },
  {
    rectangle := generatorPartitionRectangles 83 8
    coordinateU := generatorCoordinates28 1
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 20
  },
  {
    rectangle := generatorPartitionRectangles 83 9
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 83 10
    coordinateU := generatorCoordinates28 0
    coordinateV := generatorCoordinates21 0
    terms := 5
    radialRoot := generatorRadialRoots 2 20
  },
  {
    rectangle := generatorPartitionRectangles 83 11
    coordinateU := generatorCoordinates28 0
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 83 12
    coordinateU := generatorCoordinates27 7
    coordinateV := generatorCoordinates21 0
    terms := 4
    radialRoot := generatorRadialRoots 2 19
  },
  {
    rectangle := generatorPartitionRectangles 83 13
    coordinateU := generatorCoordinates27 7
    coordinateV := generatorCoordinates20 7
    terms := 3
    radialRoot := generatorRadialRoots 2 18
  },
  {
    rectangle := generatorPartitionRectangles 83 14
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates19 5
    terms := 3
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 83 15
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates18 5
    terms := 4
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 83 16
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates19 2
    terms := 2
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 83 17
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates19 1
    terms := 2
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 83 18
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates19 2
    terms := 2
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 83 19
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates19 1
    terms := 2
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 83 20
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 83 21
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 83 22
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 83 23
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 83 24
    coordinateU := generatorCoordinates25 5
    coordinateV := generatorCoordinates18 4
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 83 25
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 83 26
    coordinateU := generatorCoordinates26 4
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 83 27
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates19 0
    terms := 2
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 83 28
    coordinateU := generatorCoordinates26 3
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 83 29
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates21 0
    terms := 3
    radialRoot := generatorRadialRoots 2 18
  },
  {
    rectangle := generatorPartitionRectangles 83 30
    coordinateU := generatorCoordinates27 6
    coordinateV := generatorCoordinates20 7
    terms := 2
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 83 31
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates21 0
    terms := 2
    radialRoot := generatorRadialRoots 2 17
  },
  {
    rectangle := generatorPartitionRectangles 83 32
    coordinateU := generatorCoordinates27 5
    coordinateV := generatorCoordinates20 7
    terms := 2
    radialRoot := generatorRadialRoots 2 16
  },
  {
    rectangle := generatorPartitionRectangles 83 33
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates19 5
    terms := 2
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 83 34
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates19 6
    terms := 3
    radialRoot := generatorRadialRoots 2 15
  },
  {
    rectangle := generatorPartitionRectangles 83 35
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates19 5
    terms := 2
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 83 36
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates18 5
    terms := 3
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 83 37
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates19 6
    terms := 1
    radialRoot := generatorRadialRoots 2 14
  },
  {
    rectangle := generatorPartitionRectangles 83 38
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates19 5
    terms := 1
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 83 39
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates19 6
    terms := 1
    radialRoot := generatorRadialRoots 2 13
  },
  {
    rectangle := generatorPartitionRectangles 83 40
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates19 5
    terms := 1
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 83 41
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates19 4
    terms := 1
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 83 42
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates19 3
    terms := 1
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 83 43
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates19 4
    terms := 1
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 83 44
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates19 3
    terms := 1
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 83 45
    coordinateU := generatorCoordinates25 4
    coordinateV := generatorCoordinates18 4
    terms := 2
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 83 46
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates19 0
    terms := 1
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 83 47
    coordinateU := generatorCoordinates26 2
    coordinateV := generatorCoordinates18 7
    terms := 2
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 83 48
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates19 0
    terms := 1
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 83 49
    coordinateU := generatorCoordinates26 1
    coordinateV := generatorCoordinates18 7
    terms := 1
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 83 50
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates19 2
    terms := 1
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 83 51
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates19 1
    terms := 1
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 83 52
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates19 2
    terms := 1
    radialRoot := generatorRadialRoots 2 9
  },
  {
    rectangle := generatorPartitionRectangles 83 53
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates19 1
    terms := 1
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 83 54
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates19 0
    terms := 1
    radialRoot := generatorRadialRoots 2 8
  },
  {
    rectangle := generatorPartitionRectangles 83 55
    coordinateU := generatorCoordinates26 0
    coordinateV := generatorCoordinates18 7
    terms := 1
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 83 56
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates19 0
    terms := 1
    radialRoot := generatorRadialRoots 2 7
  },
  {
    rectangle := generatorPartitionRectangles 83 57
    coordinateU := generatorCoordinates25 7
    coordinateV := generatorCoordinates18 7
    terms := 1
    radialRoot := generatorRadialRoots 2 6
  },
  {
    rectangle := generatorPartitionRectangles 83 58
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 12
  },
  {
    rectangle := generatorPartitionRectangles 83 59
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 83 60
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates15 3
    terms := 2
    radialRoot := generatorRadialRoots 2 11
  },
  {
    rectangle := generatorPartitionRectangles 83 61
    coordinateU := generatorCoordinates26 5
    coordinateV := generatorCoordinates15 2
    terms := 2
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 83 62
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates15 1
    terms := 3
    radialRoot := generatorRadialRoots 2 10
  },
  {
    rectangle := generatorPartitionRectangles 83 63
    coordinateU := generatorCoordinates26 6
    coordinateV := generatorCoordinates15 0
    terms := 3
    radialRoot := generatorRadialRoots 2 9
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks83_valid : ∀ i, (generatorLeafBlocks83 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks83 i).coordinateU.IsValid ∧
      (generatorLeafBlocks83 i).coordinateV.IsValid ∧
      (generatorLeafBlocks83 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates28_valid 2,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 22⟩
    · exact ⟨generatorCoordinates28_valid 2,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates28_valid 1,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 21⟩
    · exact ⟨generatorCoordinates28_valid 1,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 20⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates28_valid 0,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 20⟩
    · exact ⟨generatorCoordinates28_valid 0,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates27_valid 7,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 19⟩
    · exact ⟨generatorCoordinates27_valid 7,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 18⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates25_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates26_valid 4,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates26_valid 3,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 18⟩
    · exact ⟨generatorCoordinates27_valid 6,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates21_valid 0, generatorRadialRoots_valid 2 17⟩
    · exact ⟨generatorCoordinates27_valid 5,
        generatorCoordinates20_valid 7, generatorRadialRoots_valid 2 16⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 15⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 14⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 2 13⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates25_valid 4,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates26_valid 2,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates26_valid 1,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 2 9⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 8⟩
    · exact ⟨generatorCoordinates26_valid 0,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 2 7⟩
    · exact ⟨generatorCoordinates25_valid 7,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 2 6⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 12⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 2 11⟩
    · exact ⟨generatorCoordinates26_valid 5,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 2 10⟩
    · exact ⟨generatorCoordinates26_valid 6,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 2 9⟩
  have hMeta : ∀ i, (generatorLeafBlocks83 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks83 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
