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
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20

/-!
# Checked genuine source positivity on actual generator leaves

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual source leaf candidates, block 95 of the recorded finite partition. -/
def generatorLeafBlocks95 : Fin 64 → GeneratorLeafData := ![
  {
    rectangle := generatorPartitionRectangles 95 0
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates11 6
    terms := 1
    radialRoot := generatorRadialRoots 1 29
  },
  {
    rectangle := generatorPartitionRectangles 95 1
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates11 5
    terms := 1
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 95 2
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates11 6
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 95 3
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates11 5
    terms := 0
    radialRoot := generatorRadialRoots 1 26
  },
  {
    rectangle := generatorPartitionRectangles 95 4
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates11 4
    terms := 1
    radialRoot := generatorRadialRoots 1 26
  },
  {
    rectangle := generatorPartitionRectangles 95 5
    coordinateU := generatorCoordinates20 2
    coordinateV := generatorCoordinates11 3
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 6
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates11 4
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 7
    coordinateU := generatorCoordinates20 1
    coordinateV := generatorCoordinates11 3
    terms := 1
    radialRoot := generatorRadialRoots 1 24
  },
  {
    rectangle := generatorPartitionRectangles 95 8
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates11 2
    terms := 2
    radialRoot := generatorRadialRoots 1 26
  },
  {
    rectangle := generatorPartitionRectangles 95 9
    coordinateU := generatorCoordinates20 4
    coordinateV := generatorCoordinates11 1
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 10
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates11 2
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 11
    coordinateU := generatorCoordinates20 3
    coordinateV := generatorCoordinates11 1
    terms := 1
    radialRoot := generatorRadialRoots 1 24
  },
  {
    rectangle := generatorPartitionRectangles 95 12
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 13
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates10 2
    terms := 2
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 14
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 95 15
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates11 0
    terms := 0
    radialRoot := generatorRadialRoots 1 36
  },
  {
    rectangle := generatorPartitionRectangles 95 16
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates10 7
    terms := 0
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 95 17
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates11 0
    terms := 0
    radialRoot := generatorRadialRoots 1 34
  },
  {
    rectangle := generatorPartitionRectangles 95 18
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates10 7
    terms := 0
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 95 19
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates10 6
    terms := 0
    radialRoot := generatorRadialRoots 1 31
  },
  {
    rectangle := generatorPartitionRectangles 95 20
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates10 5
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 95 21
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates10 6
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 95 22
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates10 5
    terms := 0
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 23
    coordinateU := generatorCoordinates18 3
    coordinateV := generatorCoordinates10 0
    terms := 0
    radialRoot := generatorRadialRoots 1 27
  },
  {
    rectangle := generatorPartitionRectangles 95 24
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates10 6
    terms := 0
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 25
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates10 5
    terms := 0
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 26
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates10 6
    terms := 0
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 27
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates10 5
    terms := 0
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 95 28
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates10 4
    terms := 0
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 29
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates10 3
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 30
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates10 4
    terms := 0
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 31
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates10 3
    terms := 0
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 95 32
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates10 2
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 95 33
    coordinateU := generatorCoordinates19 2
    coordinateV := generatorCoordinates10 1
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 95 34
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates10 2
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 95 35
    coordinateU := generatorCoordinates19 1
    coordinateV := generatorCoordinates10 1
    terms := 0
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 95 36
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates10 4
    terms := 0
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 95 37
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates10 3
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 95 38
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates10 4
    terms := 0
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 95 39
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates10 3
    terms := 0
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 95 40
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates10 2
    terms := 0
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 95 41
    coordinateU := generatorCoordinates19 0
    coordinateV := generatorCoordinates10 1
    terms := 0
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 95 42
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates10 2
    terms := 0
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 95 43
    coordinateU := generatorCoordinates18 7
    coordinateV := generatorCoordinates10 1
    terms := 0
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 95 44
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates6 5
    terms := 1
    radialRoot := generatorRadialRoots 1 25
  },
  {
    rectangle := generatorPartitionRectangles 95 45
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates6 4
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 46
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates6 5
    terms := 1
    radialRoot := generatorRadialRoots 1 23
  },
  {
    rectangle := generatorPartitionRectangles 95 47
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates6 4
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 95 48
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates6 3
    terms := 1
    radialRoot := generatorRadialRoots 1 22
  },
  {
    rectangle := generatorPartitionRectangles 95 49
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 95 50
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates6 3
    terms := 1
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 95 51
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates6 2
    terms := 1
    radialRoot := generatorRadialRoots 1 20
  },
  {
    rectangle := generatorPartitionRectangles 95 52
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates5 5
    terms := 4
    radialRoot := generatorRadialRoots 1 21
  },
  {
    rectangle := generatorPartitionRectangles 95 53
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates5 4
    terms := 1
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 95 54
    coordinateU := generatorCoordinates18 6
    coordinateV := generatorCoordinates5 3
    terms := 2
    radialRoot := generatorRadialRoots 1 19
  },
  {
    rectangle := generatorPartitionRectangles 95 55
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 17
  },
  {
    rectangle := generatorPartitionRectangles 95 56
    coordinateU := generatorCoordinates19 6
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 95 57
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 95 58
    coordinateU := generatorCoordinates19 5
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 95 59
    coordinateU := generatorCoordinates18 5
    coordinateV := generatorCoordinates5 3
    terms := 1
    radialRoot := generatorRadialRoots 1 15
  },
  {
    rectangle := generatorPartitionRectangles 95 60
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates5 7
    terms := 1
    radialRoot := generatorRadialRoots 1 13
  },
  {
    rectangle := generatorPartitionRectangles 95 61
    coordinateU := generatorCoordinates19 4
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 95 62
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates5 7
    terms := 0
    radialRoot := generatorRadialRoots 1 11
  },
  {
    rectangle := generatorPartitionRectangles 95 63
    coordinateU := generatorCoordinates19 3
    coordinateV := generatorCoordinates5 6
    terms := 1
    radialRoot := generatorRadialRoots 1 9
  }
]

/-- All geometry, true coordinate and radial data, and actual lower checks pass. -/
theorem generatorLeafBlocks95_valid : ∀ i, (generatorLeafBlocks95 i).IsValid := by
  have hData : ∀ i, (generatorLeafBlocks95 i).coordinateU.IsValid ∧
      (generatorLeafBlocks95 i).coordinateV.IsValid ∧
      (generatorLeafBlocks95 i).radialRoot.IsValid := by
    intro i
    fin_cases i
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 29⟩
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates11_valid 6, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates11_valid 5, generatorRadialRoots_valid 1 26⟩
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates11_valid 4, generatorRadialRoots_valid 1 26⟩
    · exact ⟨generatorCoordinates20_valid 2,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates11_valid 4, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates20_valid 1,
        generatorCoordinates11_valid 3, generatorRadialRoots_valid 1 24⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates11_valid 2, generatorRadialRoots_valid 1 26⟩
    · exact ⟨generatorCoordinates20_valid 4,
        generatorCoordinates11_valid 1, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates11_valid 2, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates20_valid 3,
        generatorCoordinates11_valid 1, generatorRadialRoots_valid 1 24⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 36⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates11_valid 0, generatorRadialRoots_valid 1 34⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates10_valid 7, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 31⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates18_valid 3,
        generatorCoordinates10_valid 0, generatorRadialRoots_valid 1 27⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates10_valid 6, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates10_valid 5, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates19_valid 2,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates19_valid 1,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates10_valid 4, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates10_valid 3, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates19_valid 0,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates10_valid 2, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates18_valid 7,
        generatorCoordinates10_valid 1, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 25⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates6_valid 5, generatorRadialRoots_valid 1 23⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates6_valid 4, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 22⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates6_valid 3, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates6_valid 2, generatorRadialRoots_valid 1 20⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates5_valid 5, generatorRadialRoots_valid 1 21⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates5_valid 4, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates18_valid 6,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 19⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 17⟩
    · exact ⟨generatorCoordinates19_valid 6,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates19_valid 5,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates18_valid 5,
        generatorCoordinates5_valid 3, generatorRadialRoots_valid 1 15⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 13⟩
    · exact ⟨generatorCoordinates19_valid 4,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates5_valid 7, generatorRadialRoots_valid 1 11⟩
    · exact ⟨generatorCoordinates19_valid 3,
        generatorCoordinates5_valid 6, generatorRadialRoots_valid 1 9⟩
  have hMeta : ∀ i, (generatorLeafBlocks95 i).MetadataValid := by
    intro i
    unfold GeneratorLeafData.MetadataValid
    fin_cases i <;> decide +kernel
  have hLower : ∀ i, 0 < (generatorLeafBlocks95 i).sparseLowerBound := by
    intro i
    unfold GeneratorLeafData.sparseLowerBound
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨(hData i).1, (hData i).2.1, (hData i).2.2,
    GeneratorLeafData.numericalValid_of_sparse (hMeta i) (hLower i)⟩

end PartialBalayage.Maximal.Square
