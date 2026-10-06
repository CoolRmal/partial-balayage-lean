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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 52 of the recorded finite partition. -/
def generatorLeafBlocks52 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 52 0
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 52 1
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 52 2
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 52 3
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 52 4
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 52 5
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 52 6
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 52 7
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 52 8
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates22 2
    terms := 12
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 52 9
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 52 10
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 52 11
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates22 1
    terms := 8
    radialRoot := generatorRadialRoots 3 27
  },
  {
    rectangle := generatorPartitionRectangles 52 12
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates22 0
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 52 13
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 26
  },
  {
    rectangle := generatorPartitionRectangles 52 14
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 52 15
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates23 1
    terms := 8
    radialRoot := generatorRadialRoots 3 25
  },
  {
    rectangle := generatorPartitionRectangles 52 16
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates23 0
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 52 17
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates22 7
    terms := 8
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 52 18
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates22 6
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 52 19
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates22 7
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 52 20
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates22 6
    terms := 5
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 52 21
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates21 7
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 52 22
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 52 23
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 52 24
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 52 25
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 52 26
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates22 5
    terms := 5
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 52 27
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates22 4
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 52 28
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates22 5
    terms := 5
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 52 29
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates22 4
    terms := 5
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 52 30
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 52 31
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 52 32
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates22 3
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 52 33
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates22 2
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 52 34
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates19 6
    terms := 12
    radialRoot := generatorRadialRoots 3 24
  },
  {
    rectangle := generatorPartitionRectangles 52 35
    coordinateU := generatorCoordinates47 7
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 52 36
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 22
  },
  {
    rectangle := generatorPartitionRectangles 52 37
    coordinateU := generatorCoordinates47 6
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 52 38
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 52 39
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 20
  },
  {
    rectangle := generatorPartitionRectangles 52 40
    coordinateU := generatorCoordinates47 5
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 52 41
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 18
  },
  {
    rectangle := generatorPartitionRectangles 52 42
    coordinateU := generatorCoordinates47 4
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 52 43
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 52 44
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 52 45
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 52 46
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 52 47
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 52 48
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 16
  },
  {
    rectangle := generatorPartitionRectangles 52 49
    coordinateU := generatorCoordinates47 3
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 52 50
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 14
  },
  {
    rectangle := generatorPartitionRectangles 52 51
    coordinateU := generatorCoordinates47 2
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 52 52
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates18 5
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 52 53
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 12
  },
  {
    rectangle := generatorPartitionRectangles 52 54
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 52 55
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates19 6
    terms := 8
    radialRoot := generatorRadialRoots 3 11
  },
  {
    rectangle := generatorPartitionRectangles 52 56
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates19 5
    terms := 8
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 52 57
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates19 4
    terms := 5
    radialRoot := generatorRadialRoots 3 10
  },
  {
    rectangle := generatorPartitionRectangles 52 58
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates19 3
    terms := 5
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 52 59
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates19 4
    terms := 5
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 52 60
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates19 3
    terms := 5
    radialRoot := generatorRadialRoots 3 8
  },
  {
    rectangle := generatorPartitionRectangles 52 61
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates18 4
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 52 62
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates18 3
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 52 63
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates19 2
    terms := 5
    radialRoot := generatorRadialRoots 3 8
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks52_valid : ∀ i, (generatorLeafBlocks52 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks52 i).coordinateU.IsValid ∧
      (generatorLeafBlocks52 i).coordinateV.IsValid ∧
      (generatorLeafBlocks52 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates22_valid 1, generatorRadialRoots_valid 3 27⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates22_valid 0, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 26⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates23_valid 1, generatorRadialRoots_valid 3 25⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates23_valid 0, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates22_valid 7, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates22_valid 6, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates21_valid 7, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates22_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates22_valid 4, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates22_valid 3, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates22_valid 2, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 24⟩
    · exact ⟨generatorCoordinates47_valid 7,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 22⟩
    · exact ⟨generatorCoordinates47_valid 6,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 20⟩
    · exact ⟨generatorCoordinates47_valid 5,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 18⟩
    · exact ⟨generatorCoordinates47_valid 4,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 16⟩
    · exact ⟨generatorCoordinates47_valid 3,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 14⟩
    · exact ⟨generatorCoordinates47_valid 2,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates18_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 12⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates19_valid 6, generatorRadialRoots_valid 3 11⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates19_valid 5, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 3 10⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates19_valid 4, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates19_valid 3, generatorRadialRoots_valid 3 8⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates18_valid 4, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates18_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 3 8⟩
  have hMeta : ∀ i, (generatorLeafBlocks52 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks52 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
