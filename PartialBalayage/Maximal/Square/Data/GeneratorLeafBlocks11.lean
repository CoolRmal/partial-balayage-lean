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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates68
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates70
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates72

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 11 of the recorded finite partition. -/
def generatorLeafBlocks11 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 11 0
    coordinateU := generatorCoordinates72 7
    coordinateV := generatorCoordinates0 3
    terms := 12
    radialRoot := generatorRadialRoots 3 50
  },
  {
    rectangle := generatorPartitionRectangles 11 1
    coordinateU := generatorCoordinates70 1
    coordinateV := generatorCoordinates36 6
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 11 2
    coordinateU := generatorCoordinates70 0
    coordinateV := generatorCoordinates36 7
    terms := 0
    radialRoot := generatorRadialRoots 5 48
  },
  {
    rectangle := generatorPartitionRectangles 11 3
    coordinateU := generatorCoordinates70 0
    coordinateV := generatorCoordinates36 6
    terms := 0
    radialRoot := generatorRadialRoots 5 47
  },
  {
    rectangle := generatorPartitionRectangles 11 4
    coordinateU := generatorCoordinates69 7
    coordinateV := generatorCoordinates32 6
    terms := 12
    radialRoot := generatorRadialRoots 5 46
  },
  {
    rectangle := generatorPartitionRectangles 11 5
    coordinateU := generatorCoordinates70 1
    coordinateV := generatorCoordinates29 1
    terms := 0
    radialRoot := generatorRadialRoots 5 44
  },
  {
    rectangle := generatorPartitionRectangles 11 6
    coordinateU := generatorCoordinates70 1
    coordinateV := generatorCoordinates29 0
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 11 7
    coordinateU := generatorCoordinates70 0
    coordinateV := generatorCoordinates29 1
    terms := 0
    radialRoot := generatorRadialRoots 5 42
  },
  {
    rectangle := generatorPartitionRectangles 11 8
    coordinateU := generatorCoordinates70 0
    coordinateV := generatorCoordinates29 0
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 11 9
    coordinateU := generatorCoordinates70 1
    coordinateV := generatorCoordinates25 2
    terms := 0
    radialRoot := generatorRadialRoots 5 37
  },
  {
    rectangle := generatorPartitionRectangles 11 10
    coordinateU := generatorCoordinates70 1
    coordinateV := generatorCoordinates25 1
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 11 11
    coordinateU := generatorCoordinates70 0
    coordinateV := generatorCoordinates25 2
    terms := 0
    radialRoot := generatorRadialRoots 5 24
  },
  {
    rectangle := generatorPartitionRectangles 11 12
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates25 4
    terms := 0
    radialRoot := generatorRadialRoots 5 22
  },
  {
    rectangle := generatorPartitionRectangles 11 13
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates25 3
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 11 14
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates25 4
    terms := 0
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 11 15
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates25 3
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 11 16
    coordinateU := generatorCoordinates70 1
    coordinateV := generatorCoordinates21 5
    terms := 4
    radialRoot := generatorRadialRoots 5 20
  },
  {
    rectangle := generatorPartitionRectangles 11 17
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates21 7
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 11 18
    coordinateU := generatorCoordinates70 5
    coordinateV := generatorCoordinates21 6
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 11 19
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates21 7
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 11 20
    coordinateU := generatorCoordinates70 4
    coordinateV := generatorCoordinates21 6
    terms := 20
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 11 21
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates22 1
    terms := 1
    radialRoot := generatorRadialRoots 5 18
  },
  {
    rectangle := generatorPartitionRectangles 11 22
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates22 0
    terms := 2
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 11 23
    coordinateU := generatorCoordinates70 2
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 5 15
  },
  {
    rectangle := generatorPartitionRectangles 11 24
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates22 7
    terms := 2
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 11 25
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates22 6
    terms := 3
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 11 26
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates22 7
    terms := 4
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 11 27
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates22 6
    terms := 5
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 11 28
    coordinateU := generatorCoordinates70 3
    coordinateV := generatorCoordinates21 7
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 11 29
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates22 3
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 11 30
    coordinateU := generatorCoordinates71 1
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 31
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 32
    coordinateU := generatorCoordinates71 0
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 11 33
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates22 5
    terms := 4
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 11 34
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates22 4
    terms := 5
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 35
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates22 5
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 36
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates22 4
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 11 37
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 11 38
    coordinateU := generatorCoordinates70 7
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 11 39
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 11 40
    coordinateU := generatorCoordinates70 6
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 4 60
  },
  {
    rectangle := generatorPartitionRectangles 11 41
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates19 6
    terms := 4
    radialRoot := generatorRadialRoots 5 13
  },
  {
    rectangle := generatorPartitionRectangles 11 42
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates19 5
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 11 43
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates19 6
    terms := 5
    radialRoot := generatorRadialRoots 5 9
  },
  {
    rectangle := generatorPartitionRectangles 11 44
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 11 45
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates19 4
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 11 46
    coordinateU := generatorCoordinates71 5
    coordinateV := generatorCoordinates19 3
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 47
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates19 4
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 48
    coordinateU := generatorCoordinates71 4
    coordinateV := generatorCoordinates19 3
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 11 49
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 5 5
  },
  {
    rectangle := generatorPartitionRectangles 11 50
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 51
    coordinateU := generatorCoordinates71 2
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 5 2
  },
  {
    rectangle := generatorPartitionRectangles 11 52
    coordinateU := generatorCoordinates71 2
    coordinateV := generatorCoordinates19 5
    terms := 12
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 11 53
    coordinateU := generatorCoordinates71 3
    coordinateV := generatorCoordinates19 4
    terms := 20
    radialRoot := generatorRadialRoots 5 0
  },
  {
    rectangle := generatorPartitionRectangles 11 54
    coordinateU := generatorCoordinates72 3
    coordinateV := generatorCoordinates20 2
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 11 55
    coordinateU := generatorCoordinates72 3
    coordinateV := generatorCoordinates20 1
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 11 56
    coordinateU := generatorCoordinates72 2
    coordinateV := generatorCoordinates20 2
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 11 57
    coordinateU := generatorCoordinates72 2
    coordinateV := generatorCoordinates20 1
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 11 58
    coordinateU := generatorCoordinates72 1
    coordinateV := generatorCoordinates20 4
    terms := 12
    radialRoot := generatorRadialRoots 4 63
  },
  {
    rectangle := generatorPartitionRectangles 11 59
    coordinateU := generatorCoordinates72 1
    coordinateV := generatorCoordinates20 3
    terms := 20
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 11 60
    coordinateU := generatorCoordinates72 0
    coordinateV := generatorCoordinates20 4
    terms := 12
    radialRoot := generatorRadialRoots 4 62
  },
  {
    rectangle := generatorPartitionRectangles 11 61
    coordinateU := generatorCoordinates72 0
    coordinateV := generatorCoordinates20 3
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 11 62
    coordinateU := generatorCoordinates72 1
    coordinateV := generatorCoordinates20 2
    terms := 20
    radialRoot := generatorRadialRoots 4 61
  },
  {
    rectangle := generatorPartitionRectangles 11 63
    coordinateU := generatorCoordinates72 1
    coordinateV := generatorCoordinates20 1
    terms := 30
    radialRoot := generatorRadialRoots 4 60
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks11_valid : ∀ i, (generatorLeafBlocks11 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks11 i).coordinateU.IsValid ∧
      (generatorLeafBlocks11 i).coordinateV.IsValid ∧
      (generatorLeafBlocks11 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates72_valid 7,
        generatorCoordinates0_valid 3, generatorRadialRoots_valid 3 50⟩
    · exact ⟨generatorCoordinates70_valid 1,
        generatorCoordinates36_valid 6, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates70_valid 0,
        generatorCoordinates36_valid 7, generatorRadialRoots_valid 5 48⟩
    · exact ⟨generatorCoordinates70_valid 0,
        generatorCoordinates36_valid 6, generatorRadialRoots_valid 5 47⟩
    · exact ⟨generatorCoordinates69_valid 7,
        generatorCoordinates32_valid 6, generatorRadialRoots_valid 5 46⟩
    · exact ⟨generatorCoordinates70_valid 1,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 5 44⟩
    · exact ⟨generatorCoordinates70_valid 1,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates70_valid 0,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 5 42⟩
    · exact ⟨generatorCoordinates70_valid 0,
        generatorCoordinates29_valid 0, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates70_valid 1,
        generatorCoordinates25_valid 2, generatorRadialRoots_valid 5 37⟩
    · exact ⟨generatorCoordinates70_valid 1,
        generatorCoordinates25_valid 1, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates70_valid 0,
        generatorCoordinates25_valid 2, generatorRadialRoots_valid 5 24⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 5 22⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates70_valid 1,
        generatorCoordinates21_valid 5, generatorRadialRoots_valid 5 20⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates70_valid 5,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates70_valid 4,
        generatorCoordinates21_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 5 18⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates70_valid 2,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 5 15⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates70_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates71_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates71_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates70_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates70_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 4 60⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 5 13⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 5 9⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates71_valid 5,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates71_valid 4,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 5 5⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates71_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 5 2⟩
    · exact ⟨generatorCoordinates71_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates71_valid 3,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 5 0⟩
    · exact ⟨generatorCoordinates72_valid 3,
        generatorCoordinates20_valid 2, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates72_valid 3,
        generatorCoordinates20_valid 1, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates72_valid 2,
        generatorCoordinates20_valid 2, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates72_valid 2,
        generatorCoordinates20_valid 1, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates72_valid 1,
        generatorCoordinates20_valid 4, generatorRadialRoots_valid 4 63⟩
    · exact ⟨generatorCoordinates72_valid 1,
        generatorCoordinates20_valid 3, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates72_valid 0,
        generatorCoordinates20_valid 4, generatorRadialRoots_valid 4 62⟩
    · exact ⟨generatorCoordinates72_valid 0,
        generatorCoordinates20_valid 3, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates72_valid 1,
        generatorCoordinates20_valid 2, generatorRadialRoots_valid 4 61⟩
    · exact ⟨generatorCoordinates72_valid 1,
        generatorCoordinates20_valid 1, generatorRadialRoots_valid 4 60⟩
  have hMeta : ∀ i, (generatorLeafBlocks11 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks11 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
