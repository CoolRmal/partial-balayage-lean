/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafFastCheck
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates0
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates88
public import PartialBalayage.Maximal.Square.GeneratorRadialRoots

/-!
# The actual first generator leaf using shared checked data

This concrete leaf reuses the genuine coordinate and radial root tables. Its
positive rational lower bound is computed by the ordinary Lean kernel and feeds
the proved pointwise generator soundness theorem.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- The actual first dyadic source rectangle with shared coordinate and root data. -/
def firstCachedGeneratorLeaf : GeneratorLeafData where
  rectangle := ⟨27, 0, 1, 1, 0⟩
  coordinateU := generatorCoordinates88 7
  coordinateV := generatorCoordinates0 1
  terms := 0
  radialRoot := generatorRadialRoots 5 48

/-- Its actual source rectangle lower bound is strictly positive. -/
theorem firstCachedGeneratorLeaf_fastLowerBound_pos :
    0 < firstCachedGeneratorLeaf.fastLowerBound := by
  unfold GeneratorLeafData.fastLowerBound
  decide +kernel

/-- All actual data and geometry checks for this concrete leaf pass. -/
theorem firstCachedGeneratorLeaf_valid : firstCachedGeneratorLeaf.IsValid := by
  refine ⟨generatorCoordinates88_valid 7, generatorCoordinates0_valid 1,
    generatorRadialRoots_valid 5 48, ?_⟩
  apply GeneratorLeafData.numericalValid_of_fast
  · unfold GeneratorLeafData.MetadataValid
    decide +kernel
  · exact firstCachedGeneratorLeaf_fastLowerBound_pos

/-- The shared-data check implies genuine pointwise positivity on the entire leaf. -/
theorem generatorInteriorDensity_pos_first_cached_leaf {u v : ℝ}
    (h : firstCachedGeneratorLeaf.rectangle.Contains u v)
    (hu : 0 < u) (hv : 0 < v) (hr : u + v < 28) :
    0 < generatorInteriorDensity u v :=
  GeneratorLeafData.positivity firstCachedGeneratorLeaf_valid h hu hv hr

end PartialBalayage.Maximal.Square
