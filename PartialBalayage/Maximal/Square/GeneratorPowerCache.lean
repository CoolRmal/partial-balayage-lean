/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache0
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache1
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache2
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache3
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache4
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache5
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache6
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache7
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache8
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache9
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache10
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache11
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache12
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache13
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache14
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache15
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache16
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache17
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache18
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache19
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache20
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache21
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache22
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache23
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache24
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache25
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache26
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache27
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache28
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache29
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache30
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache31
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache32
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache33
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache34
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache35
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache36
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache37
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache38
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache39
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache40
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache41
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache42
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache43
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache44
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache45
public import PartialBalayage.Maximal.Square.Data.GeneratorPowerCache46

/-!
# Shared checked power data for all actual generator rectangles

The finite table combines independently kernel-checked positive-center data.
Signed Taylor centers reuse these actual root bounds through reflection.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- All shared genuine positive-center Taylor data used by the partition. -/
def generatorPowerCache : Fin 47 → Fin 64 → GeneratorPowerTaylorData := ![
  generatorPowerCache0,
  generatorPowerCache1,
  generatorPowerCache2,
  generatorPowerCache3,
  generatorPowerCache4,
  generatorPowerCache5,
  generatorPowerCache6,
  generatorPowerCache7,
  generatorPowerCache8,
  generatorPowerCache9,
  generatorPowerCache10,
  generatorPowerCache11,
  generatorPowerCache12,
  generatorPowerCache13,
  generatorPowerCache14,
  generatorPowerCache15,
  generatorPowerCache16,
  generatorPowerCache17,
  generatorPowerCache18,
  generatorPowerCache19,
  generatorPowerCache20,
  generatorPowerCache21,
  generatorPowerCache22,
  generatorPowerCache23,
  generatorPowerCache24,
  generatorPowerCache25,
  generatorPowerCache26,
  generatorPowerCache27,
  generatorPowerCache28,
  generatorPowerCache29,
  generatorPowerCache30,
  generatorPowerCache31,
  generatorPowerCache32,
  generatorPowerCache33,
  generatorPowerCache34,
  generatorPowerCache35,
  generatorPowerCache36,
  generatorPowerCache37,
  generatorPowerCache38,
  generatorPowerCache39,
  generatorPowerCache40,
  generatorPowerCache41,
  generatorPowerCache42,
  generatorPowerCache43,
  generatorPowerCache44,
  generatorPowerCache45,
  generatorPowerCache46
]

/-- Each shared datum satisfies the actual rational root and Taylor-error checks. -/
theorem generatorPowerCache_valid (b : Fin 47) (i : Fin 64) :
    (generatorPowerCache b i).IsValid := by
  fin_cases b
  · exact generatorPowerCache0_valid i
  · exact generatorPowerCache1_valid i
  · exact generatorPowerCache2_valid i
  · exact generatorPowerCache3_valid i
  · exact generatorPowerCache4_valid i
  · exact generatorPowerCache5_valid i
  · exact generatorPowerCache6_valid i
  · exact generatorPowerCache7_valid i
  · exact generatorPowerCache8_valid i
  · exact generatorPowerCache9_valid i
  · exact generatorPowerCache10_valid i
  · exact generatorPowerCache11_valid i
  · exact generatorPowerCache12_valid i
  · exact generatorPowerCache13_valid i
  · exact generatorPowerCache14_valid i
  · exact generatorPowerCache15_valid i
  · exact generatorPowerCache16_valid i
  · exact generatorPowerCache17_valid i
  · exact generatorPowerCache18_valid i
  · exact generatorPowerCache19_valid i
  · exact generatorPowerCache20_valid i
  · exact generatorPowerCache21_valid i
  · exact generatorPowerCache22_valid i
  · exact generatorPowerCache23_valid i
  · exact generatorPowerCache24_valid i
  · exact generatorPowerCache25_valid i
  · exact generatorPowerCache26_valid i
  · exact generatorPowerCache27_valid i
  · exact generatorPowerCache28_valid i
  · exact generatorPowerCache29_valid i
  · exact generatorPowerCache30_valid i
  · exact generatorPowerCache31_valid i
  · exact generatorPowerCache32_valid i
  · exact generatorPowerCache33_valid i
  · exact generatorPowerCache34_valid i
  · exact generatorPowerCache35_valid i
  · exact generatorPowerCache36_valid i
  · exact generatorPowerCache37_valid i
  · exact generatorPowerCache38_valid i
  · exact generatorPowerCache39_valid i
  · exact generatorPowerCache40_valid i
  · exact generatorPowerCache41_valid i
  · exact generatorPowerCache42_valid i
  · exact generatorPowerCache43_valid i
  · exact generatorPowerCache44_valid i
  · exact generatorPowerCache45_valid i
  · exact generatorPowerCache46_valid i

end PartialBalayage.Maximal.Square
