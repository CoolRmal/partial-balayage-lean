/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots
public import PartialBalayage.Maximal.Square.GeneratorPartitionRectangles
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
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

/-- Actual source leaf candidates, block 53 of the recorded finite partition. -/
def generatorLeafBlocks53 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 53 0
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates19 1
    terms := 5
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 53 1
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates19 2
    terms := 5
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 53 2
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates19 1
    terms := 5
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 53 3
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates19 0
    terms := 5
    radialRoot := generatorRadialRoots 3 6
  },
  {
    rectangle := generatorPartitionRectangles 53 4
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates18 7
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 53 5
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates19 0
    terms := 5
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 53 6
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates18 7
    terms := 5
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 53 7
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 9
  },
  {
    rectangle := generatorPartitionRectangles 53 8
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 53 9
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 7
  },
  {
    rectangle := generatorPartitionRectangles 53 10
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 53 11
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 53 12
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 53 13
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 53 14
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 53 15
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates14 3
    terms := 8
    radialRoot := generatorRadialRoots 3 5
  },
  {
    rectangle := generatorPartitionRectangles 53 16
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates14 2
    terms := 8
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 53 17
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates15 3
    terms := 5
    radialRoot := generatorRadialRoots 3 4
  },
  {
    rectangle := generatorPartitionRectangles 53 18
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates15 2
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 53 19
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates15 3
    terms := 5
    radialRoot := generatorRadialRoots 3 3
  },
  {
    rectangle := generatorPartitionRectangles 53 20
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates15 2
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 53 21
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates15 1
    terms := 5
    radialRoot := generatorRadialRoots 3 2
  },
  {
    rectangle := generatorPartitionRectangles 53 22
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates15 0
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 53 23
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates15 1
    terms := 5
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 53 24
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates15 0
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 53 25
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates14 1
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 53 26
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates14 0
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 53 27
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates14 7
    terms := 5
    radialRoot := generatorRadialRoots 3 0
  },
  {
    rectangle := generatorPartitionRectangles 53 28
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates14 6
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 53 29
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates14 7
    terms := 5
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 53 30
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates14 6
    terms := 5
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 53 31
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 62
  },
  {
    rectangle := generatorPartitionRectangles 53 32
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 53 33
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates14 5
    terms := 4
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 53 34
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates14 4
    terms := 4
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 53 35
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 3 1
  },
  {
    rectangle := generatorPartitionRectangles 53 36
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 53 37
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 2 63
  },
  {
    rectangle := generatorPartitionRectangles 53 38
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 53 39
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 53 40
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 53 41
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 53 42
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 53 43
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates10 0
    terms := 8
    radialRoot := generatorRadialRoots 2 61
  },
  {
    rectangle := generatorPartitionRectangles 53 44
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates9 7
    terms := 8
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 53 45
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 59
  },
  {
    rectangle := generatorPartitionRectangles 53 46
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 53 47
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates11 0
    terms := 4
    radialRoot := generatorRadialRoots 2 57
  },
  {
    rectangle := generatorPartitionRectangles 53 48
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates10 7
    terms := 4
    radialRoot := generatorRadialRoots 2 55
  },
  {
    rectangle := generatorPartitionRectangles 53 49
    coordinateU := generatorCoordinates46 4
    coordinateV := generatorCoordinates9 7
    terms := 12
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 53 50
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates9 6
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 53 51
    coordinateU := generatorCoordinates46 5
    coordinateV := generatorCoordinates9 5
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 53 52
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates10 4
    terms := 4
    radialRoot := generatorRadialRoots 2 51
  },
  {
    rectangle := generatorPartitionRectangles 53 53
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates10 3
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 53 54
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates10 4
    terms := 4
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 53 55
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates10 3
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 53 56
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates10 2
    terms := 4
    radialRoot := generatorRadialRoots 2 47
  },
  {
    rectangle := generatorPartitionRectangles 53 57
    coordinateU := generatorCoordinates47 1
    coordinateV := generatorCoordinates10 1
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 53 58
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates10 2
    terms := 4
    radialRoot := generatorRadialRoots 2 45
  },
  {
    rectangle := generatorPartitionRectangles 53 59
    coordinateU := generatorCoordinates47 0
    coordinateV := generatorCoordinates10 1
    terms := 4
    radialRoot := generatorRadialRoots 2 44
  },
  {
    rectangle := generatorPartitionRectangles 53 60
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 2 53
  },
  {
    rectangle := generatorPartitionRectangles 53 61
    coordinateU := generatorCoordinates46 7
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 53 62
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates5 5
    terms := 8
    radialRoot := generatorRadialRoots 2 49
  },
  {
    rectangle := generatorPartitionRectangles 53 63
    coordinateU := generatorCoordinates46 6
    coordinateV := generatorCoordinates5 4
    terms := 8
    radialRoot := generatorRadialRoots 2 45
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks53_valid : ∀ i, (generatorLeafBlocks53 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks53 i).coordinateU.IsValid ∧
      (generatorLeafBlocks53 i).coordinateV.IsValid ∧
      (generatorLeafBlocks53 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates19_valid 2, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates19_valid 1, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 3 6⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates19_valid 0, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates18_valid 7, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 9⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 7⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates14_valid 3, generatorRadialRoots_valid 3 5⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates14_valid 2, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 3 4⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates15_valid 3, generatorRadialRoots_valid 3 3⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates15_valid 2, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 3 2⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates15_valid 1, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates15_valid 0, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates14_valid 1, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates14_valid 0, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 3 0⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates14_valid 7, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates14_valid 6, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 62⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates14_valid 5, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates14_valid 4, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 3 1⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 2 63⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 2 61⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 59⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 2 57⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 2 55⟩
    · exact ⟨generatorCoordinates46_valid 4,
        generatorCoordinates9_valid 7, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates9_valid 6, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates46_valid 5,
        generatorCoordinates9_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 51⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 47⟩
    · exact ⟨generatorCoordinates47_valid 1,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 2 45⟩
    · exact ⟨generatorCoordinates47_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 2 44⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 53⟩
    · exact ⟨generatorCoordinates46_valid 7,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 2 49⟩
    · exact ⟨generatorCoordinates46_valid 6,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 2 45⟩
  have hMeta : ∀ i, (generatorLeafBlocks53 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks53 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
