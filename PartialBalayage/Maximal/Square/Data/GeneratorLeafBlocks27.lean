/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates58
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates60

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 27 of the recorded finite partition. -/
def generatorLeafBlocks27 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 27 0
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates34 0
    terms := 20
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 27 1
    coordinateU := generatorCoordinates60 4
    coordinateV := generatorCoordinates33 7
    terms := 20
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 27 2
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates33 1
    terms := 30
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 27 3
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 4 44
  },
  {
    rectangle := generatorPartitionRectangles 27 4
    coordinateU := generatorCoordinates60 3
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 27 5
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates34 0
    terms := 12
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 27 6
    coordinateU := generatorCoordinates60 2
    coordinateV := generatorCoordinates33 7
    terms := 12
    radialRoot := generatorRadialRoots 4 40
  },
  {
    rectangle := generatorPartitionRectangles 27 7
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates33 1
    terms := 20
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 27 8
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates29 5
    terms := 8
    radialRoot := generatorRadialRoots 4 48
  },
  {
    rectangle := generatorPartitionRectangles 27 9
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates29 4
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 27 10
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates29 5
    terms := 8
    radialRoot := generatorRadialRoots 4 42
  },
  {
    rectangle := generatorPartitionRectangles 27 11
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates29 4
    terms := 8
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 27 12
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates29 3
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 27 13
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 27 14
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates29 3
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 27 15
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 27 16
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates29 5
    terms := 12
    radialRoot := generatorRadialRoots 4 38
  },
  {
    rectangle := generatorPartitionRectangles 27 17
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates29 4
    terms := 12
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 27 18
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates29 5
    terms := 20
    radialRoot := generatorRadialRoots 4 34
  },
  {
    rectangle := generatorPartitionRectangles 27 19
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates29 4
    terms := 20
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 27 20
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates29 3
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 27 21
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 27 22
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates29 3
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 27 23
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates29 2
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 27 24
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 4 32
  },
  {
    rectangle := generatorPartitionRectangles 27 25
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates26 5
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 27 26
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates26 6
    terms := 12
    radialRoot := generatorRadialRoots 4 30
  },
  {
    rectangle := generatorPartitionRectangles 27 27
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates26 5
    terms := 20
    radialRoot := generatorRadialRoots 4 28
  },
  {
    rectangle := generatorPartitionRectangles 27 28
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates25 5
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 27 29
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates25 6
    terms := 20
    radialRoot := generatorRadialRoots 4 26
  },
  {
    rectangle := generatorPartitionRectangles 27 30
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates25 5
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 27 31
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates25 4
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 27 32
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 27 33
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates25 4
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 27 34
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 27 35
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates25 6
    terms := 20
    radialRoot := generatorRadialRoots 4 22
  },
  {
    rectangle := generatorPartitionRectangles 27 36
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates25 5
    terms := 20
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 27 37
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates25 6
    terms := 12
    radialRoot := generatorRadialRoots 4 17
  },
  {
    rectangle := generatorPartitionRectangles 27 38
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates25 5
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 27 39
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates25 4
    terms := 20
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 27 40
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 27 41
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates25 4
    terms := 20
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 27 42
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates25 3
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 27 43
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 4 9
  },
  {
    rectangle := generatorPartitionRectangles 27 44
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 27 45
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates22 1
    terms := 12
    radialRoot := generatorRadialRoots 4 5
  },
  {
    rectangle := generatorPartitionRectangles 27 46
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 27 47
    coordinateU := generatorCoordinates60 1
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 27 48
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 63
  },
  {
    rectangle := generatorPartitionRectangles 27 49
    coordinateU := generatorCoordinates61 1
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 27 50
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 27 51
    coordinateU := generatorCoordinates61 0
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 27 52
    coordinateU := generatorCoordinates60 0
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 27 53
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 59
  },
  {
    rectangle := generatorPartitionRectangles 27 54
    coordinateU := generatorCoordinates60 7
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 27 55
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 27 56
    coordinateU := generatorCoordinates60 6
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 27 57
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates22 1
    terms := 20
    radialRoot := generatorRadialRoots 4 1
  },
  {
    rectangle := generatorPartitionRectangles 27 58
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 27 59
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates22 1
    terms := 20
    radialRoot := generatorRadialRoots 3 61
  },
  {
    rectangle := generatorPartitionRectangles 27 60
    coordinateU := generatorCoordinates59 6
    coordinateV := generatorCoordinates22 0
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 27 61
    coordinateU := generatorCoordinates59 7
    coordinateV := generatorCoordinates21 7
    terms := 12
    radialRoot := generatorRadialRoots 3 57
  },
  {
    rectangle := generatorPartitionRectangles 27 62
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates22 3
    terms := 12
    radialRoot := generatorRadialRoots 3 56
  },
  {
    rectangle := generatorPartitionRectangles 27 63
    coordinateU := generatorCoordinates60 5
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 54
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks27_valid : ∀ i, (generatorLeafBlocks27 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks27 i).coordinateU.IsValid ∧
      (generatorLeafBlocks27 i).coordinateV.IsValid ∧
      (generatorLeafBlocks27 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates60_valid 4,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 44⟩
    · exact ⟨generatorCoordinates60_valid 3,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates34_valid 0, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates60_valid 2,
        generatorCoordinates33_valid 7, generatorRadialRoots_valid 4 40⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates33_valid 1, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 48⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 42⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 38⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 4 34⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 4 32⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 4 30⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 4 28⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 26⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 22⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 4 17⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 9⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 5⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates60_valid 1,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 63⟩
    · exact ⟨generatorCoordinates61_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates61_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates60_valid 0,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 59⟩
    · exact ⟨generatorCoordinates60_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates60_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 4 1⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 61⟩
    · exact ⟨generatorCoordinates59_valid 6,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates59_valid 7,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 57⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 56⟩
    · exact ⟨generatorCoordinates60_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 54⟩
  have hMeta : ∀ i, (generatorLeafBlocks27 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks27 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
