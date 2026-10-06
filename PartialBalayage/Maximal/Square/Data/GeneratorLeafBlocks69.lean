/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31
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

/-- Actual source leaf candidates, block 69 of the recorded finite partition. -/
def generatorLeafBlocks69 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 69 0
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates32 1
    terms := 8
    radialRoot := generatorRadialRoots 3 21
  },
  {
    rectangle := generatorPartitionRectangles 69 1
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates32 0
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 69 2
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates32 1
    terms := 5
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 69 3
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates32 0
    terms := 8
    radialRoot := generatorRadialRoots 3 19
  },
  {
    rectangle := generatorPartitionRectangles 69 4
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates31 7
    terms := 8
    radialRoot := generatorRadialRoots 3 19
  },
  {
    rectangle := generatorPartitionRectangles 69 5
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates31 6
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 69 6
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates31 7
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 69 7
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates31 6
    terms := 8
    radialRoot := generatorRadialRoots 3 17
  },
  {
    rectangle := generatorPartitionRectangles 69 8
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates30 3
    terms := 5
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 69 9
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 69 10
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates29 5
    terms := 4
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 69 11
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates29 4
    terms := 5
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 69 12
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates31 5
    terms := 8
    radialRoot := generatorRadialRoots 3 17
  },
  {
    rectangle := generatorPartitionRectangles 69 13
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates31 4
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 69 14
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates31 5
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 69 15
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates31 4
    terms := 8
    radialRoot := generatorRadialRoots 3 15
  },
  {
    rectangle := generatorPartitionRectangles 69 16
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates31 3
    terms := 8
    radialRoot := generatorRadialRoots 3 15
  },
  {
    rectangle := generatorPartitionRectangles 69 17
    coordinateU := generatorCoordinates36 4
    coordinateV := generatorCoordinates31 2
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 69 18
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates31 3
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 69 19
    coordinateU := generatorCoordinates36 3
    coordinateV := generatorCoordinates31 2
    terms := 8
    radialRoot := generatorRadialRoots 3 13
  },
  {
    rectangle := generatorPartitionRectangles 69 20
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 69 21
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 69 22
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 69 23
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 69 24
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 69 25
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 69 26
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates29 3
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 69 27
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates29 2
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 69 28
    coordinateU := generatorCoordinates32 7
    coordinateV := generatorCoordinates29 1
    terms := 4
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 69 29
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates29 3
    terms := 4
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 69 30
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates29 2
    terms := 5
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 69 31
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates29 3
    terms := 4
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 69 32
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates29 2
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 69 33
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 69 34
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 69 35
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 69 36
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 69 37
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 69 38
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 69 39
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 69 40
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 69 41
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates25 6
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 69 42
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 69 43
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 69 44
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 69 45
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 69 46
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 69 47
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 69 48
    coordinateU := generatorCoordinates34 4
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 69 49
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 69 50
    coordinateU := generatorCoordinates34 3
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 69 51
    coordinateU := generatorCoordinates33 3
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 69 52
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 69 53
    coordinateU := generatorCoordinates34 2
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 69 54
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 69 55
    coordinateU := generatorCoordinates34 1
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 69 56
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates25 6
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 69 57
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 69 58
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates25 6
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 69 59
    coordinateU := generatorCoordinates33 1
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 69 60
    coordinateU := generatorCoordinates33 2
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 69 61
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 69 62
    coordinateU := generatorCoordinates34 0
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 69 63
    coordinateU := generatorCoordinates33 7
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks69_valid : ∀ i, (generatorLeafBlocks69 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks69 i).coordinateU.IsValid ∧
      (generatorLeafBlocks69 i).coordinateV.IsValid ∧
      (generatorLeafBlocks69 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates32_valid 1, generatorRadialRoots_valid 3 21⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates32_valid 0, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates32_valid 1, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates32_valid 0, generatorRadialRoots_valid 3 19⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 3 19⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 3 17⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates29_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates29_valid 4, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 3 17⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 3 15⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates31_valid 3, generatorRadialRoots_valid 3 15⟩
    · exact ⟨generatorCoordinates36_valid 4,
        generatorCoordinates31_valid 2, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates31_valid 3, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates36_valid 3,
        generatorCoordinates31_valid 2, generatorRadialRoots_valid 3 13⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates32_valid 7,
        generatorCoordinates29_valid 1, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates29_valid 2, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates34_valid 4,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates34_valid 3,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates33_valid 3,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates34_valid 2,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates34_valid 1,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates33_valid 1,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates33_valid 2,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates34_valid 0,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates33_valid 7,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 2 63⟩
  have hMeta : ∀ i, (generatorLeafBlocks69 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks69 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
