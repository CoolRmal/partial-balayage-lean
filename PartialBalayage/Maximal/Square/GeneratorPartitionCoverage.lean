/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorUnitCellCover
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionTrees0
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionTrees1
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionTrees2
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionTrees3
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionTrees4
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRemainingTrees

/-!
# Genuine coverage by the checked generator partition

The finite roots are checked against all ordered integer unit cells in the
strict support triangle. Actual floor-cell coverage and the sound subdivision
lemma then give a genuine labeled rectangle containing every required point.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- The 210 proposed subdivision trees for the ordered integer root cells. -/
def generatorPartitionTrees : Fin 21 → Fin 10 →
    GeneratorPartitionTree (Fin 106 × Fin 64) := ![
  generatorPartitionTrees0,
  generatorPartitionTrees1,
  generatorPartitionTrees2,
  generatorPartitionTrees3,
  generatorPartitionTrees4,
  generatorPartitionTrees5,
  generatorPartitionTrees6,
  generatorPartitionTrees7,
  generatorPartitionTrees8,
  generatorPartitionTrees9,
  generatorPartitionTrees10,
  generatorPartitionTrees11,
  generatorPartitionTrees12,
  generatorPartitionTrees13,
  generatorPartitionTrees14,
  generatorPartitionTrees15,
  generatorPartitionTrees16,
  generatorPartitionTrees17,
  generatorPartitionTrees18,
  generatorPartitionTrees19,
  generatorPartitionTrees20
]

/-- All branches, leaf identities and exterior pruning inequalities are checked. -/
theorem generatorPartitionTrees_valid (b : Fin 21) (i : Fin 10) :
    (generatorPartitionTrees b i).IsValid
      (fun p ↦ generatorPartitionRectangles p.1 p.2) := by
  fin_cases b
  · exact generatorPartitionTrees0_valid i
  · exact generatorPartitionTrees1_valid i
  · exact generatorPartitionTrees2_valid i
  · exact generatorPartitionTrees3_valid i
  · exact generatorPartitionTrees4_valid i
  · exact generatorPartitionTrees5_valid i
  · exact generatorPartitionTrees6_valid i
  · exact generatorPartitionTrees7_valid i
  · exact generatorPartitionTrees8_valid i
  · exact generatorPartitionTrees9_valid i
  · exact generatorPartitionTrees10_valid i
  · exact generatorPartitionTrees11_valid i
  · exact generatorPartitionTrees12_valid i
  · exact generatorPartitionTrees13_valid i
  · exact generatorPartitionTrees14_valid i
  · exact generatorPartitionTrees15_valid i
  · exact generatorPartitionTrees16_valid i
  · exact generatorPartitionTrees17_valid i
  · exact generatorPartitionTrees18_valid i
  · exact generatorPartitionTrees19_valid i
  · exact generatorPartitionTrees20_valid i

/-- The actual finite tree roots contain every ordered integer unit cell needed inside support. -/
theorem generatorPartitionTrees_root_cover : ∀ i j : Fin 28,
    j.val ≤ i.val → i.val + j.val < 28 →
      ∃ b : Fin 21, ∃ k : Fin 10,
        (generatorPartitionTrees b k).root = generatorUnitRectangle i.val j.val := by
  decide +kernel

/-- Every point in the actual ordered generator region belongs to a checked leaf rectangle. -/
theorem exists_generatorPartitionRectangle_contains {u v : ℝ}
    (hv : 0 < v) (hvu : v ≤ u) (hr : u + v < 28) :
    ∃ p : Fin 106 × Fin 64, (generatorPartitionRectangles p.1 p.2).Contains u v := by
  obtain ⟨i, j, hij, hs, hcell⟩ := exists_generatorUnitRectangle_contains hv hvu hr
  obtain ⟨b, k, hroot⟩ := generatorPartitionTrees_root_cover i j hij hs
  exact GeneratorPartitionTree.coverage (generatorPartitionTrees_valid b k)
    (hroot.symm ▸ hcell) hr

end PartialBalayage.Maximal.Square
