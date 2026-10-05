/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.NormalizedGeneratorCellMatrices0
public import PartialBalayage.Maximal.Square.Data.NormalizedGeneratorCellMatrices1
public import PartialBalayage.Maximal.Square.Data.NormalizedGeneratorCellMatrices2
public import PartialBalayage.Maximal.Square.Data.NormalizedGeneratorCellMatrices3
public import PartialBalayage.Maximal.Square.Data.NormalizedGeneratorCellMatrices4
public import PartialBalayage.Maximal.Square.Data.NormalizedGeneratorCellMatrices5
public import PartialBalayage.Maximal.Square.Data.NormalizedGeneratorCellMatrices6
public import PartialBalayage.Maximal.Square.GeneratorCellCoefficients

/-!
# Normalized cache of the actual generator-cell coefficients

The finite cache has the exact original values. Its direct rational structure
literals avoid repeating gcd normalization inside later certificate checks.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The original exact generator coefficient table, using directly reduced literals. -/
def normalizedGeneratorCellCoefficients : Fin 28 → Fin 53 → Fin 4 → ℚ := ![
  normalizedGeneratorCellMatrix0,
  normalizedGeneratorCellMatrix1,
  normalizedGeneratorCellMatrix2,
  normalizedGeneratorCellMatrix3,
  normalizedGeneratorCellMatrix4,
  normalizedGeneratorCellMatrix5,
  normalizedGeneratorCellMatrix6,
  normalizedGeneratorCellMatrix7,
  normalizedGeneratorCellMatrix8,
  normalizedGeneratorCellMatrix9,
  normalizedGeneratorCellMatrix10,
  normalizedGeneratorCellMatrix11,
  normalizedGeneratorCellMatrix12,
  normalizedGeneratorCellMatrix13,
  normalizedGeneratorCellMatrix14,
  normalizedGeneratorCellMatrix15,
  normalizedGeneratorCellMatrix16,
  normalizedGeneratorCellMatrix17,
  normalizedGeneratorCellMatrix18,
  normalizedGeneratorCellMatrix19,
  normalizedGeneratorCellMatrix20,
  normalizedGeneratorCellMatrix21,
  normalizedGeneratorCellMatrix22,
  normalizedGeneratorCellMatrix23,
  normalizedGeneratorCellMatrix24,
  normalizedGeneratorCellMatrix25,
  normalizedGeneratorCellMatrix26,
  normalizedGeneratorCellMatrix27
]

/-- The normalized table is exactly the original actual coefficient table. -/
theorem normalizedGeneratorCellCoefficients_eq :
    normalizedGeneratorCellCoefficients = generatorCellCoefficients := by
  funext cell
  fin_cases cell
  · exact normalizedGeneratorCellMatrix0_eq
  · exact normalizedGeneratorCellMatrix1_eq
  · exact normalizedGeneratorCellMatrix2_eq
  · exact normalizedGeneratorCellMatrix3_eq
  · exact normalizedGeneratorCellMatrix4_eq
  · exact normalizedGeneratorCellMatrix5_eq
  · exact normalizedGeneratorCellMatrix6_eq
  · exact normalizedGeneratorCellMatrix7_eq
  · exact normalizedGeneratorCellMatrix8_eq
  · exact normalizedGeneratorCellMatrix9_eq
  · exact normalizedGeneratorCellMatrix10_eq
  · exact normalizedGeneratorCellMatrix11_eq
  · exact normalizedGeneratorCellMatrix12_eq
  · exact normalizedGeneratorCellMatrix13_eq
  · exact normalizedGeneratorCellMatrix14_eq
  · exact normalizedGeneratorCellMatrix15_eq
  · exact normalizedGeneratorCellMatrix16_eq
  · exact normalizedGeneratorCellMatrix17_eq
  · exact normalizedGeneratorCellMatrix18_eq
  · exact normalizedGeneratorCellMatrix19_eq
  · exact normalizedGeneratorCellMatrix20_eq
  · exact normalizedGeneratorCellMatrix21_eq
  · exact normalizedGeneratorCellMatrix22_eq
  · exact normalizedGeneratorCellMatrix23_eq
  · exact normalizedGeneratorCellMatrix24_eq
  · exact normalizedGeneratorCellMatrix25_eq
  · exact normalizedGeneratorCellMatrix26_eq
  · exact normalizedGeneratorCellMatrix27_eq

end PartialBalayage.Maximal.Square
