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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates28
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates72
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates74
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates76

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 8 of the recorded finite partition. -/
def generatorLeafBlocks8 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 8 0
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates1 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 8 1
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates1 6
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 8 2
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates1 5
    terms := 12
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 8 3
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates0 5
    terms := 30
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 8 4
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 13
  },
  {
    rectangle := generatorPartitionRectangles 8 5
    coordinateU := generatorCoordinates76 3
    coordinateV := generatorCoordinates1 1
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 8 6
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 8 7
    coordinateU := generatorCoordinates76 2
    coordinateV := generatorCoordinates1 1
    terms := 12
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 8 8
    coordinateU := generatorCoordinates75 5
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 8 9
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 7
  },
  {
    rectangle := generatorPartitionRectangles 8 10
    coordinateU := generatorCoordinates76 1
    coordinateV := generatorCoordinates1 1
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 8 11
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates1 2
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 8 12
    coordinateU := generatorCoordinates76 0
    coordinateV := generatorCoordinates1 1
    terms := 20
    radialRoot := generatorRadialRoots 4 3
  },
  {
    rectangle := generatorPartitionRectangles 8 13
    coordinateU := generatorCoordinates75 4
    coordinateV := generatorCoordinates0 3
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 8 14
    coordinateU := generatorCoordinates72 6
    coordinateV := generatorCoordinates32 7
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 8 15
    coordinateU := generatorCoordinates72 5
    coordinateV := generatorCoordinates33 0
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 8 16
    coordinateU := generatorCoordinates72 5
    coordinateV := generatorCoordinates32 7
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 8 17
    coordinateU := generatorCoordinates72 4
    coordinateV := generatorCoordinates28 7
    terms := 12
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 8 18
    coordinateU := generatorCoordinates72 6
    coordinateV := generatorCoordinates25 2
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 8 19
    coordinateU := generatorCoordinates72 6
    coordinateV := generatorCoordinates25 1
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 8 20
    coordinateU := generatorCoordinates72 5
    coordinateV := generatorCoordinates25 2
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 8 21
    coordinateU := generatorCoordinates72 5
    coordinateV := generatorCoordinates25 1
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 8 22
    coordinateU := generatorCoordinates72 6
    coordinateV := generatorCoordinates21 5
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 8 23
    coordinateU := generatorCoordinates72 6
    coordinateV := generatorCoordinates21 4
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 8 24
    coordinateU := generatorCoordinates72 5
    coordinateV := generatorCoordinates21 5
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 8 25
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates21 7
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 8 26
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates21 6
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 8 27
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates21 7
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 8 28
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates21 6
    terms := 2
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 8 29
    coordinateU := generatorCoordinates72 6
    coordinateV := generatorCoordinates18 2
    terms := 4
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 8 30
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates18 4
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 8 31
    coordinateU := generatorCoordinates73 2
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 8 32
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates18 4
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 8 33
    coordinateU := generatorCoordinates73 1
    coordinateV := generatorCoordinates18 3
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 8 34
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates18 6
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 8 35
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates18 5
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 8 36
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates18 6
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 8 37
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates19 4
    terms := 2
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 8 38
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates19 3
    terms := 3
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 8 39
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates19 4
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 8 40
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates19 3
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 8 41
    coordinateU := generatorCoordinates73 0
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 8 42
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates19 0
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 8 43
    coordinateU := generatorCoordinates73 6
    coordinateV := generatorCoordinates18 7
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 8 44
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates19 0
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 8 45
    coordinateU := generatorCoordinates73 5
    coordinateV := generatorCoordinates18 7
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 8 46
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates19 2
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 8 47
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates19 1
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 8 48
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates19 2
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 8 49
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates19 1
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 8 50
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates19 0
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 8 51
    coordinateU := generatorCoordinates73 4
    coordinateV := generatorCoordinates18 7
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 8 52
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates19 0
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 8 53
    coordinateU := generatorCoordinates73 3
    coordinateV := generatorCoordinates18 7
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 8 54
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates15 3
    terms := 4
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 8 55
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates15 2
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 8 56
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates15 3
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 8 57
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates15 2
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 8 58
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates15 1
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 8 59
    coordinateU := generatorCoordinates74 2
    coordinateV := generatorCoordinates15 0
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 8 60
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates15 1
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 8 61
    coordinateU := generatorCoordinates74 1
    coordinateV := generatorCoordinates15 0
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 8 62
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates15 3
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 8 63
    coordinateU := generatorCoordinates74 0
    coordinateV := generatorCoordinates15 2
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks8_valid : ∀ i, (generatorLeafBlocks8 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks8 i).coordinateU.IsValid ∧
      (generatorLeafBlocks8 i).coordinateV.IsValid ∧
      (generatorLeafBlocks8 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates1_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates1_valid 5, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates0_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 13⟩
    · exact ⟨generatorCoordinates76_valid 3,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates76_valid 2,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates75_valid 5,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 7⟩
    · exact ⟨generatorCoordinates76_valid 1,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates1_valid 2, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates76_valid 0,
        generatorCoordinates1_valid 1, generatorRadialRoots_valid 4 3⟩
    · exact ⟨generatorCoordinates75_valid 4,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates72_valid 6,
        generatorCoordinates32_valid 7, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates72_valid 5,
        generatorCoordinates33_valid 0, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates72_valid 5,
        generatorCoordinates32_valid 7, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates72_valid 4,
        generatorCoordinates28_valid 7, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates72_valid 6,
        generatorCoordinates25_valid 2, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates72_valid 6,
        generatorCoordinates25_valid 1, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates72_valid 5,
        generatorCoordinates25_valid 2, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates72_valid 5,
        generatorCoordinates25_valid 1, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates72_valid 6,
        generatorCoordinates21_valid 5, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates72_valid 6,
        generatorCoordinates21_valid 4, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates72_valid 5,
        generatorCoordinates21_valid 5, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates72_valid 6,
        generatorCoordinates18_valid 2, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates73_valid 2,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates73_valid 1,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates18_valid 6, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates73_valid 0,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates73_valid 6,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates73_valid 5,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates73_valid 4,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates73_valid 3,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates74_valid 2,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates74_valid 1,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates74_valid 0,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 5 2⟩
  have hMeta : ∀ i, (generatorLeafBlocks8 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks8 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
