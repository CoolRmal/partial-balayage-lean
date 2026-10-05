/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.GeneratorRadialRoots0
public import PartialBalayage.Maximal.Square.Data.GeneratorRadialRoots1
public import PartialBalayage.Maximal.Square.Data.GeneratorRadialRoots2
public import PartialBalayage.Maximal.Square.Data.GeneratorRadialRoots3
public import PartialBalayage.Maximal.Square.Data.GeneratorRadialRoots4
public import PartialBalayage.Maximal.Square.Data.GeneratorRadialRoots5

/-!
# Kernel-checked shared radial roots for the actual generator rectangles

The six finite blocks contain exact enclosures for all 369 distinct positive tangent
radii used by the genuine rectangle partition. Padding repeats the first valid datum.
Every enclosure passes ordinary kernel arithmetic and bounds its actual real power.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Shared actual radial root data, indexed by finite block and finite position. -/
def generatorRadialRoots : Fin 6 → Fin 64 → GeneratorRadialRootData :=
  ![generatorRadialRoots0, generatorRadialRoots1, generatorRadialRoots2,
    generatorRadialRoots3, generatorRadialRoots4, generatorRadialRoots5]

/-- Every shared radius and both negative-power enclosures satisfy the exact kernel checks. -/
theorem generatorRadialRoots_valid (b : Fin 6) (i : Fin 64) :
    (generatorRadialRoots b i).IsValid := by
  fin_cases b
  · exact generatorRadialRoots0_valid i
  · exact generatorRadialRoots1_valid i
  · exact generatorRadialRoots2_valid i
  · exact generatorRadialRoots3_valid i
  · exact generatorRadialRoots4_valid i
  · exact generatorRadialRoots5_valid i

/-- Each shared datum supplies a genuine valid radial tangent for every finite tail choice. -/
theorem generatorRadialRoots_plane_valid (b : Fin 6) (i : Fin 64)
    (difference : ℚ) (terms : Fin 76) :
    ((generatorRadialRoots b i).plane difference terms).IsValid :=
  GeneratorRadialRootData.plane_valid (generatorRadialRoots_valid b i) difference terms

end PartialBalayage.Maximal.Square
