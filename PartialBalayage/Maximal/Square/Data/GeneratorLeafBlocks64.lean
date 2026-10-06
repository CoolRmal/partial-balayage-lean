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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 64 of the recorded finite partition. -/
def generatorLeafBlocks64 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 64 0
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates30 3
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 64 1
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates30 2
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 64 2
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates32 1
    terms := 8
    radialRoot := generatorRadialRoots 3 23
  },
  {
    rectangle := generatorPartitionRectangles 64 3
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates32 0
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 64 4
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates32 1
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 64 5
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates32 0
    terms := 8
    radialRoot := generatorRadialRoots 3 21
  },
  {
    rectangle := generatorPartitionRectangles 64 6
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates31 7
    terms := 8
    radialRoot := generatorRadialRoots 3 21
  },
  {
    rectangle := generatorPartitionRectangles 64 7
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates31 6
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 64 8
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates31 7
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 64 9
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates31 6
    terms := 8
    radialRoot := generatorRadialRoots 3 19
  },
  {
    rectangle := generatorPartitionRectangles 64 10
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates29 3
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 64 11
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates29 7
    terms := 5
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 64 12
    coordinateU := generatorCoordinates37 7
    coordinateV := generatorCoordinates29 6
    terms := 5
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 64 13
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 64 14
    coordinateU := generatorCoordinates37 6
    coordinateV := generatorCoordinates29 6
    terms := 5
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 64 15
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates30 1
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 64 16
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates30 0
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 64 17
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates31 5
    terms := 8
    radialRoot := generatorRadialRoots 3 19
  },
  {
    rectangle := generatorPartitionRectangles 64 18
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates31 4
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 64 19
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates31 5
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 64 20
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates31 4
    terms := 8
    radialRoot := generatorRadialRoots 3 17
  },
  {
    rectangle := generatorPartitionRectangles 64 21
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates31 3
    terms := 8
    radialRoot := generatorRadialRoots 3 17
  },
  {
    rectangle := generatorPartitionRectangles 64 22
    coordinateU := generatorCoordinates38 5
    coordinateV := generatorCoordinates31 2
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 64 23
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates31 3
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 64 24
    coordinateU := generatorCoordinates38 4
    coordinateV := generatorCoordinates31 2
    terms := 8
    radialRoot := generatorRadialRoots 3 15
  },
  {
    rectangle := generatorPartitionRectangles 64 25
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates29 7
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 64 26
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 64 27
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates29 7
    terms := 12
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 64 28
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates29 6
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 64 29
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates25 6
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 64 30
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates25 5
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 64 31
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates25 6
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 64 32
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates25 5
    terms := 5
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 64 33
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 64 34
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates25 3
    terms := 12
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 64 35
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 64 36
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates25 3
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 64 37
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates25 6
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 64 38
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates25 5
    terms := 5
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 64 39
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates26 6
    terms := 5
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 64 40
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates26 5
    terms := 5
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 64 41
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates26 6
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 64 42
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates26 5
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 64 43
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates26 4
    terms := 5
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 64 44
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates26 3
    terms := 5
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 64 45
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates26 4
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 64 46
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates26 3
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 64 47
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates25 4
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 64 48
    coordinateU := generatorCoordinates37 1
    coordinateV := generatorCoordinates25 3
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 64 49
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 64 50
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 64 51
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates26 2
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 64 52
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates26 1
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 64 53
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 64 54
    coordinateU := generatorCoordinates37 5
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 64 55
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates26 0
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 64 56
    coordinateU := generatorCoordinates37 4
    coordinateV := generatorCoordinates25 7
    terms := 8
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 64 57
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 64 58
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 64 59
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 64 60
    coordinateU := generatorCoordinates37 2
    coordinateV := generatorCoordinates22 0
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 64 61
    coordinateU := generatorCoordinates37 3
    coordinateV := generatorCoordinates21 7
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 64 62
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates22 3
    terms := 5
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 64 63
    coordinateU := generatorCoordinates38 3
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks64_valid : ∀ i, (generatorLeafBlocks64 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks64 i).coordinateU.IsValid ∧
      (generatorLeafBlocks64 i).coordinateV.IsValid ∧
      (generatorLeafBlocks64 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates30_valid 3, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates30_valid 2, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates32_valid 1, generatorRadialRoots_valid 3 23⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates32_valid 0, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates32_valid 1, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates32_valid 0, generatorRadialRoots_valid 3 21⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 3 21⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates31_valid 7, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates31_valid 6, generatorRadialRoots_valid 3 19⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates29_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates37_valid 7,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates37_valid 6,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates30_valid 1, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates30_valid 0, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 3 19⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates31_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates31_valid 4, generatorRadialRoots_valid 3 17⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates31_valid 3, generatorRadialRoots_valid 3 17⟩
    · exact ⟨generatorCoordinates38_valid 5,
        generatorCoordinates31_valid 2, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates31_valid 3, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates38_valid 4,
        generatorCoordinates31_valid 2, generatorRadialRoots_valid 3 15⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates29_valid 7, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates29_valid 6, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates25_valid 6, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates25_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates26_valid 6, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates26_valid 5, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates26_valid 4, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates26_valid 3, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates25_valid 4, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates37_valid 1,
        generatorCoordinates25_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates26_valid 2, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates26_valid 1, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates37_valid 5,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates26_valid 0, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates37_valid 4,
        generatorCoordinates25_valid 7, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates37_valid 2,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates37_valid 3,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates38_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 3⟩
  have hMeta : ∀ i, (generatorLeafBlocks64 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks64 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
