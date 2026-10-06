/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates0
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates1
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates2
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates3
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates4
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates5
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates6
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates7
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates8
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates9
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates10
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates11
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates12
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates13
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates14
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates15
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates16
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates17
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates18
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates19
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates20
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates21
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates22
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates23
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates24
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates25
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates26
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates27
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates28
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates29
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates30
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates31
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates32
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates34
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates36
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates38
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates40
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates42
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates44
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates46
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates48
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates50
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates52
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates54
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates56
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates58
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates60
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates62
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates64
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates66
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates68
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates70
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates72
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates74
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates76
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates78
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates80
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates82
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates84
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates86
public import PartialBalayage.Maximal.Square.Data.GeneratorCoordinates88

/-!
# All genuine coordinate intervals of the source partition

The checked finite blocks identify every cubic, Bernstein bound, signed Taylor
center, and Taylor radius with the actual coordinate interval.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- All actual checked coordinate intervals used by the generator partition. -/
def generatorCoordinates : Fin 89 → Fin 8 → GeneratorCoordinateData := ![
  generatorCoordinates0,
  generatorCoordinates1,
  generatorCoordinates2,
  generatorCoordinates3,
  generatorCoordinates4,
  generatorCoordinates5,
  generatorCoordinates6,
  generatorCoordinates7,
  generatorCoordinates8,
  generatorCoordinates9,
  generatorCoordinates10,
  generatorCoordinates11,
  generatorCoordinates12,
  generatorCoordinates13,
  generatorCoordinates14,
  generatorCoordinates15,
  generatorCoordinates16,
  generatorCoordinates17,
  generatorCoordinates18,
  generatorCoordinates19,
  generatorCoordinates20,
  generatorCoordinates21,
  generatorCoordinates22,
  generatorCoordinates23,
  generatorCoordinates24,
  generatorCoordinates25,
  generatorCoordinates26,
  generatorCoordinates27,
  generatorCoordinates28,
  generatorCoordinates29,
  generatorCoordinates30,
  generatorCoordinates31,
  generatorCoordinates32,
  generatorCoordinates33,
  generatorCoordinates34,
  generatorCoordinates35,
  generatorCoordinates36,
  generatorCoordinates37,
  generatorCoordinates38,
  generatorCoordinates39,
  generatorCoordinates40,
  generatorCoordinates41,
  generatorCoordinates42,
  generatorCoordinates43,
  generatorCoordinates44,
  generatorCoordinates45,
  generatorCoordinates46,
  generatorCoordinates47,
  generatorCoordinates48,
  generatorCoordinates49,
  generatorCoordinates50,
  generatorCoordinates51,
  generatorCoordinates52,
  generatorCoordinates53,
  generatorCoordinates54,
  generatorCoordinates55,
  generatorCoordinates56,
  generatorCoordinates57,
  generatorCoordinates58,
  generatorCoordinates59,
  generatorCoordinates60,
  generatorCoordinates61,
  generatorCoordinates62,
  generatorCoordinates63,
  generatorCoordinates64,
  generatorCoordinates65,
  generatorCoordinates66,
  generatorCoordinates67,
  generatorCoordinates68,
  generatorCoordinates69,
  generatorCoordinates70,
  generatorCoordinates71,
  generatorCoordinates72,
  generatorCoordinates73,
  generatorCoordinates74,
  generatorCoordinates75,
  generatorCoordinates76,
  generatorCoordinates77,
  generatorCoordinates78,
  generatorCoordinates79,
  generatorCoordinates80,
  generatorCoordinates81,
  generatorCoordinates82,
  generatorCoordinates83,
  generatorCoordinates84,
  generatorCoordinates85,
  generatorCoordinates86,
  generatorCoordinates87,
  generatorCoordinates88
]

set_option maxRecDepth 32768 in
/-- Every selected coordinate datum satisfies its actual coefficient and metadata checks. -/
theorem generatorCoordinates_valid (b : Fin 89) (i : Fin 8) :
    (generatorCoordinates b i).IsValid := by
  fin_cases b
  · exact generatorCoordinates0_valid i
  · exact generatorCoordinates1_valid i
  · exact generatorCoordinates2_valid i
  · exact generatorCoordinates3_valid i
  · exact generatorCoordinates4_valid i
  · exact generatorCoordinates5_valid i
  · exact generatorCoordinates6_valid i
  · exact generatorCoordinates7_valid i
  · exact generatorCoordinates8_valid i
  · exact generatorCoordinates9_valid i
  · exact generatorCoordinates10_valid i
  · exact generatorCoordinates11_valid i
  · exact generatorCoordinates12_valid i
  · exact generatorCoordinates13_valid i
  · exact generatorCoordinates14_valid i
  · exact generatorCoordinates15_valid i
  · exact generatorCoordinates16_valid i
  · exact generatorCoordinates17_valid i
  · exact generatorCoordinates18_valid i
  · exact generatorCoordinates19_valid i
  · exact generatorCoordinates20_valid i
  · exact generatorCoordinates21_valid i
  · exact generatorCoordinates22_valid i
  · exact generatorCoordinates23_valid i
  · exact generatorCoordinates24_valid i
  · exact generatorCoordinates25_valid i
  · exact generatorCoordinates26_valid i
  · exact generatorCoordinates27_valid i
  · exact generatorCoordinates28_valid i
  · exact generatorCoordinates29_valid i
  · exact generatorCoordinates30_valid i
  · exact generatorCoordinates31_valid i
  · exact generatorCoordinates32_valid i
  · exact generatorCoordinates33_valid i
  · exact generatorCoordinates34_valid i
  · exact generatorCoordinates35_valid i
  · exact generatorCoordinates36_valid i
  · exact generatorCoordinates37_valid i
  · exact generatorCoordinates38_valid i
  · exact generatorCoordinates39_valid i
  · exact generatorCoordinates40_valid i
  · exact generatorCoordinates41_valid i
  · exact generatorCoordinates42_valid i
  · exact generatorCoordinates43_valid i
  · exact generatorCoordinates44_valid i
  · exact generatorCoordinates45_valid i
  · exact generatorCoordinates46_valid i
  · exact generatorCoordinates47_valid i
  · exact generatorCoordinates48_valid i
  · exact generatorCoordinates49_valid i
  · exact generatorCoordinates50_valid i
  · exact generatorCoordinates51_valid i
  · exact generatorCoordinates52_valid i
  · exact generatorCoordinates53_valid i
  · exact generatorCoordinates54_valid i
  · exact generatorCoordinates55_valid i
  · exact generatorCoordinates56_valid i
  · exact generatorCoordinates57_valid i
  · exact generatorCoordinates58_valid i
  · exact generatorCoordinates59_valid i
  · exact generatorCoordinates60_valid i
  · exact generatorCoordinates61_valid i
  · exact generatorCoordinates62_valid i
  · exact generatorCoordinates63_valid i
  · exact generatorCoordinates64_valid i
  · exact generatorCoordinates65_valid i
  · exact generatorCoordinates66_valid i
  · exact generatorCoordinates67_valid i
  · exact generatorCoordinates68_valid i
  · exact generatorCoordinates69_valid i
  · exact generatorCoordinates70_valid i
  · exact generatorCoordinates71_valid i
  · exact generatorCoordinates72_valid i
  · exact generatorCoordinates73_valid i
  · exact generatorCoordinates74_valid i
  · exact generatorCoordinates75_valid i
  · exact generatorCoordinates76_valid i
  · exact generatorCoordinates77_valid i
  · exact generatorCoordinates78_valid i
  · exact generatorCoordinates79_valid i
  · exact generatorCoordinates80_valid i
  · exact generatorCoordinates81_valid i
  · exact generatorCoordinates82_valid i
  · exact generatorCoordinates83_valid i
  · exact generatorCoordinates84_valid i
  · exact generatorCoordinates85_valid i
  · exact generatorCoordinates86_valid i
  · exact generatorCoordinates87_valid i
  · exact generatorCoordinates88_valid i

end PartialBalayage.Maximal.Square
