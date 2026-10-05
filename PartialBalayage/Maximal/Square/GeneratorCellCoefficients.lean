/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix0
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix1
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix2
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix3
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix4
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix5
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix6
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix7
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix8
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix9
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix10
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix11
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix12
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix13
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix14
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix15
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix16
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix17
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix18
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix19
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix20
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix21
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix22
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix23
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix24
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix25
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix26
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix27
public import PartialBalayage.Maximal.Square.SplineGeneratorCellPolynomial

/-!
# Genuine signed generator coefficients on all partition cells

Every entry is identified with the actual signed spline generator coefficient by
the already checked finite tables. The combined table supplies the real cubic
evaluation without introducing a further arithmetic or graph hypothesis.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The proved actual cubic generator rows for all twenty-eight partition cells. -/
def generatorCellCoefficients : Fin 28 → Fin 53 → Fin 4 → ℚ := ![
  generatorCellMatrix0,
  generatorCellMatrix1,
  generatorCellMatrix2,
  generatorCellMatrix3,
  generatorCellMatrix4,
  generatorCellMatrix5,
  generatorCellMatrix6,
  generatorCellMatrix7,
  generatorCellMatrix8,
  generatorCellMatrix9,
  generatorCellMatrix10,
  generatorCellMatrix11,
  generatorCellMatrix12,
  generatorCellMatrix13,
  generatorCellMatrix14,
  generatorCellMatrix15,
  generatorCellMatrix16,
  generatorCellMatrix17,
  generatorCellMatrix18,
  generatorCellMatrix19,
  generatorCellMatrix20,
  generatorCellMatrix21,
  generatorCellMatrix22,
  generatorCellMatrix23,
  generatorCellMatrix24,
  generatorCellMatrix25,
  generatorCellMatrix26,
  generatorCellMatrix27
]

/-- Every entry of the combined table is the genuine generator-cell coefficient. -/
theorem generatorCellCoefficients_correct (cell : Fin 28) (k : Fin 53) (b : Fin 4) :
    splineGeneratorCellCoefficient (cell.val : ℤ) ((k.val : ℤ) - 26) b =
      generatorCellCoefficients cell k b := by
  fin_cases cell
  · exact generatorCellMatrix0_correct k b
  · exact generatorCellMatrix1_correct k b
  · exact generatorCellMatrix2_correct k b
  · exact generatorCellMatrix3_correct k b
  · exact generatorCellMatrix4_correct k b
  · exact generatorCellMatrix5_correct k b
  · exact generatorCellMatrix6_correct k b
  · exact generatorCellMatrix7_correct k b
  · exact generatorCellMatrix8_correct k b
  · exact generatorCellMatrix9_correct k b
  · exact generatorCellMatrix10_correct k b
  · exact generatorCellMatrix11_correct k b
  · exact generatorCellMatrix12_correct k b
  · exact generatorCellMatrix13_correct k b
  · exact generatorCellMatrix14_correct k b
  · exact generatorCellMatrix15_correct k b
  · exact generatorCellMatrix16_correct k b
  · exact generatorCellMatrix17_correct k b
  · exact generatorCellMatrix18_correct k b
  · exact generatorCellMatrix19_correct k b
  · exact generatorCellMatrix20_correct k b
  · exact generatorCellMatrix21_correct k b
  · exact generatorCellMatrix22_correct k b
  · exact generatorCellMatrix23_correct k b
  · exact generatorCellMatrix24_correct k b
  · exact generatorCellMatrix25_correct k b
  · exact generatorCellMatrix26_correct k b
  · exact generatorCellMatrix27_correct k b

/-- The actual closed-cell cubic evaluates to the proved finite coefficient row. -/
theorem splineGeneratorCellPolynomial_eq_generatorCellCoefficients
    (cell : Fin 28) (k : Fin 53) (s : ℝ) :
    splineGeneratorCellPolynomial (cell.val : ℤ) ((k.val : ℤ) - 26) s =
      centeredCubic (fun b ↦ (generatorCellCoefficients cell k b : ℝ)) s := by
  rw [splineGeneratorCellPolynomial_eq_centeredCubic]
  simp_rw [generatorCellCoefficients_correct]

end PartialBalayage.Maximal.Square
