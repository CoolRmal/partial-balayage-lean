/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.ExactRationalLiteral
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix8
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix9
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix10
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix11

/-!
# Normalized exact generator-cell coefficient cache

Each directly reduced rational is checked by Lean's ordinary kernel, and the
whole finite table is identified with the already proved actual coefficients.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Directly reduced exact coefficient rows for actual generator cell 8. -/
def normalizedGeneratorCellMatrix8 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral 752865296771777 60000000000000000),
    (exactRationalLiteral (-752865296771777) 20000000000000000),
    (exactRationalLiteral 752865296771777 20000000000000000),
    (exactRationalLiteral (-752865296771777) 60000000000000000)
  ],
  ![
    (exactRationalLiteral 86641834747143 5000000000000000),
    (exactRationalLiteral 2479131570598223 25000000000000000),
    (exactRationalLiteral (-4368511116500907) 25000000000000000),
    (exactRationalLiteral 5313200889452249 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-2378707769202221) 25000000000000000),
    (exactRationalLiteral (-1184778163439747) 25000000000000000),
    (exactRationalLiteral 16038117813486207 50000000000000000),
    (exactRationalLiteral (-49309903790619329) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1441812087722093 20000000000000000),
    (exactRationalLiteral (-7486000285646047) 100000000000000000),
    (exactRationalLiteral (-29466755905482453) 100000000000000000),
    (exactRationalLiteral 30293563664291083 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-54058697099177) 12500000000000000),
    (exactRationalLiteral 4079671414618827 50000000000000000),
    (exactRationalLiteral 7117695760296189 50000000000000000),
    (exactRationalLiteral (-42886178452196317) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-4608042128137) 3125000000000000),
    (exactRationalLiteral (-1280283089477397) 50000000000000000),
    (exactRationalLiteral (-2014649928938409) 50000000000000000),
    (exactRationalLiteral 18288129042431239 300000000000000000)
  ],
  ![
    (exactRationalLiteral 2308202398570141 300000000000000000),
    (exactRationalLiteral 186258892036801 20000000000000000),
    (exactRationalLiteral 1201861410053593 100000000000000000),
    (exactRationalLiteral (-1052052299280457) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 4131126972620123 300000000000000000),
    (exactRationalLiteral 202174591447601 20000000000000000),
    (exactRationalLiteral 2192011809263 4000000000000000),
    (exactRationalLiteral 998688384442559 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-2676521536101071) 100000000000000000),
    (exactRationalLiteral (-29115384617337) 4000000000000000),
    (exactRationalLiteral 475179699508629 100000000000000000),
    (exactRationalLiteral 1723846026535917 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-637744755288719) 25000000000000000),
    (exactRationalLiteral (-1607194859085567) 50000000000000000),
    (exactRationalLiteral (-1119959466418167) 50000000000000000),
    (exactRationalLiteral (-24241318195940651) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 8568813985829011 300000000000000000),
    (exactRationalLiteral 2759748287544031 100000000000000000),
    (exactRationalLiteral 216325171324097 20000000000000000),
    (exactRationalLiteral 19792214228530501 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-728501520957809) 300000000000000000),
    (exactRationalLiteral 96805694611501 100000000000000000),
    (exactRationalLiteral 978511407726637 100000000000000000),
    (exactRationalLiteral (-196490273352629) 9375000000000000)
  ],
  ![
    (exactRationalLiteral 40038179607619 60000000000000000),
    (exactRationalLiteral 78752704212973 100000000000000000),
    (exactRationalLiteral (-190680973200701) 20000000000000000),
    (exactRationalLiteral 180828051367037 60000000000000000)
  ],
  ![
    (exactRationalLiteral 222439850090833 30000000000000000),
    (exactRationalLiteral (-305755602092959) 50000000000000000),
    (exactRationalLiteral 188706232746401 50000000000000000),
    (exactRationalLiteral (-2977885648789) 2343750000000000)
  ],
  ![
    (exactRationalLiteral 263381604456893 9375000000000000),
    (exactRationalLiteral (-747196329451729) 50000000000000000),
    (exactRationalLiteral 124839463428073 25000000000000000),
    (exactRationalLiteral (-306899883589667) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-189261036501229) 12500000000000000),
    (exactRationalLiteral 158932825883419 12500000000000000),
    (exactRationalLiteral (-276098403989691) 50000000000000000),
    (exactRationalLiteral 12753354937973 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-165088796038881) 10000000000000000),
    (exactRationalLiteral 155302267803913 25000000000000000),
    (exactRationalLiteral (-85615418855817) 50000000000000000),
    (exactRationalLiteral 160616560360031 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-241231833581281) 50000000000000000),
    (exactRationalLiteral 79726180890907 50000000000000000),
    (exactRationalLiteral 16036165066161 25000000000000000),
    (exactRationalLiteral (-54353166483171) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-8305874674326991) 100000000000000000),
    (exactRationalLiteral 754483835369453 20000000000000000),
    (exactRationalLiteral (-1075762559269377) 100000000000000000),
    (exactRationalLiteral 122039474097137 60000000000000000)
  ],
  ![
    (exactRationalLiteral 26104258996393151 150000000000000000),
    (exactRationalLiteral (-835940526684099) 10000000000000000),
    (exactRationalLiteral 1153766953128797 50000000000000000),
    (exactRationalLiteral (-196301193326517) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-8305874674326991) 100000000000000000),
    (exactRationalLiteral 754483835369453 20000000000000000),
    (exactRationalLiteral (-1075762559269377) 100000000000000000),
    (exactRationalLiteral 122039474097137 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-241231833581281) 50000000000000000),
    (exactRationalLiteral 79726180890907 50000000000000000),
    (exactRationalLiteral 16036165066161 25000000000000000),
    (exactRationalLiteral (-54353166483171) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-165088796038881) 10000000000000000),
    (exactRationalLiteral 155302267803913 25000000000000000),
    (exactRationalLiteral (-85615418855817) 50000000000000000),
    (exactRationalLiteral 160616560360031 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-189261036501229) 12500000000000000),
    (exactRationalLiteral 158932825883419 12500000000000000),
    (exactRationalLiteral (-276098403989691) 50000000000000000),
    (exactRationalLiteral 12753354937973 12500000000000000)
  ],
  ![
    (exactRationalLiteral 263381604456893 9375000000000000),
    (exactRationalLiteral (-747196329451729) 50000000000000000),
    (exactRationalLiteral 124839463428073 25000000000000000),
    (exactRationalLiteral (-306899883589667) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 222439850090833 30000000000000000),
    (exactRationalLiteral (-305755602092959) 50000000000000000),
    (exactRationalLiteral 188706232746401 50000000000000000),
    (exactRationalLiteral (-2977885648789) 2343750000000000)
  ],
  ![
    (exactRationalLiteral 40038179607619 60000000000000000),
    (exactRationalLiteral 78752704212973 100000000000000000),
    (exactRationalLiteral (-190680973200701) 20000000000000000),
    (exactRationalLiteral 180828051367037 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-728501520957809) 300000000000000000),
    (exactRationalLiteral 96805694611501 100000000000000000),
    (exactRationalLiteral 978511407726637 100000000000000000),
    (exactRationalLiteral (-196490273352629) 9375000000000000)
  ],
  ![
    (exactRationalLiteral 8568813985829011 300000000000000000),
    (exactRationalLiteral 2759748287544031 100000000000000000),
    (exactRationalLiteral 216325171324097 20000000000000000),
    (exactRationalLiteral 19792214228530501 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-637744755288719) 25000000000000000),
    (exactRationalLiteral (-1607194859085567) 50000000000000000),
    (exactRationalLiteral (-1119959466418167) 50000000000000000),
    (exactRationalLiteral (-24241318195940651) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-2676521536101071) 100000000000000000),
    (exactRationalLiteral (-29115384617337) 4000000000000000),
    (exactRationalLiteral 475179699508629 100000000000000000),
    (exactRationalLiteral 1723846026535917 50000000000000000)
  ],
  ![
    (exactRationalLiteral 4131126972620123 300000000000000000),
    (exactRationalLiteral 202174591447601 20000000000000000),
    (exactRationalLiteral 2192011809263 4000000000000000),
    (exactRationalLiteral 998688384442559 150000000000000000)
  ],
  ![
    (exactRationalLiteral 2308202398570141 300000000000000000),
    (exactRationalLiteral 186258892036801 20000000000000000),
    (exactRationalLiteral 1201861410053593 100000000000000000),
    (exactRationalLiteral (-1052052299280457) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-4608042128137) 3125000000000000),
    (exactRationalLiteral (-1280283089477397) 50000000000000000),
    (exactRationalLiteral (-2014649928938409) 50000000000000000),
    (exactRationalLiteral 18288129042431239 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-54058697099177) 12500000000000000),
    (exactRationalLiteral 4079671414618827 50000000000000000),
    (exactRationalLiteral 7117695760296189 50000000000000000),
    (exactRationalLiteral (-42886178452196317) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1441812087722093 20000000000000000),
    (exactRationalLiteral (-7486000285646047) 100000000000000000),
    (exactRationalLiteral (-29466755905482453) 100000000000000000),
    (exactRationalLiteral 30293563664291083 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-2378707769202221) 25000000000000000),
    (exactRationalLiteral (-1184778163439747) 25000000000000000),
    (exactRationalLiteral 16038117813486207 50000000000000000),
    (exactRationalLiteral (-49309903790619329) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 86641834747143 5000000000000000),
    (exactRationalLiteral 2479131570598223 25000000000000000),
    (exactRationalLiteral (-4368511116500907) 25000000000000000),
    (exactRationalLiteral 5313200889452249 75000000000000000)
  ],
  ![
    (exactRationalLiteral 752865296771777 60000000000000000),
    (exactRationalLiteral (-752865296771777) 20000000000000000),
    (exactRationalLiteral 752865296771777 20000000000000000),
    (exactRationalLiteral (-752865296771777) 60000000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix8_eq :
    normalizedGeneratorCellMatrix8 = generatorCellMatrix8 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix8 j a = generatorCellMatrix8 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 9. -/
def normalizedGeneratorCellMatrix9 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral 472344886475671 37500000000000000),
    (exactRationalLiteral (-472344886475671) 12500000000000000),
    (exactRationalLiteral 472344886475671 12500000000000000),
    (exactRationalLiteral (-472344886475671) 37500000000000000)
  ],
  ![
    (exactRationalLiteral 4156971898594297 300000000000000000),
    (exactRationalLiteral 10103454809566511 100000000000000000),
    (exactRationalLiteral (-3446733632729383) 20000000000000000),
    (exactRationalLiteral 20798774840687117 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-28643959928971939) 300000000000000000),
    (exactRationalLiteral (-5832384768028787) 100000000000000000),
    (exactRationalLiteral 31120371423099713 100000000000000000),
    (exactRationalLiteral (-46447636186158697) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 23000615866913531 300000000000000000),
    (exactRationalLiteral (-6256052581773907) 100000000000000000),
    (exactRationalLiteral (-28650786931603939) 100000000000000000),
    (exactRationalLiteral 26945036698976473 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1923841112364749) 300000000000000000),
    (exactRationalLiteral 7668963147722809 100000000000000000),
    (exactRationalLiteral 14258829184554421 100000000000000000),
    (exactRationalLiteral (-2127089624263657) 18750000000000000)
  ],
  ![
    (exactRationalLiteral 2395356213600193 300000000000000000),
    (exactRationalLiteral (-2977296515391551) 100000000000000000),
    (exactRationalLiteral (-5110452385629149) 100000000000000000),
    (exactRationalLiteral (-563266099067809) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 3108507832971327 100000000000000000),
    (exactRationalLiteral 3117850316586273 100000000000000000),
    (exactRationalLiteral 2052177064116693 100000000000000000),
    (exactRationalLiteral 4404803472473617 18750000000000000)
  ],
  ![
    (exactRationalLiteral 518465601045967 100000000000000000),
    (exactRationalLiteral 2113110188559867 20000000000000000),
    (exactRationalLiteral 10818255858724131 100000000000000000),
    (exactRationalLiteral (-154244935466861561) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-48257181212427683) 300000000000000000),
    (exactRationalLiteral (-31935545779784453) 100000000000000000),
    (exactRationalLiteral (-5296247425755397) 20000000000000000),
    (exactRationalLiteral 53699376594889417 100000000000000000)
  ],
  ![
    (exactRationalLiteral 1994257532342653 15000000000000000),
    (exactRationalLiteral 12357607114657751 50000000000000000),
    (exactRationalLiteral 10436920042575493 50000000000000000),
    (exactRationalLiteral (-15910306462989143) 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-1263412987075841) 100000000000000000),
    (exactRationalLiteral (-4233860237219353) 100000000000000000),
    (exactRationalLiteral (-5309177339557491) 100000000000000000),
    (exactRationalLiteral 4333771823778993 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-126635444208193) 25000000000000000),
    (exactRationalLiteral (-230979192739713) 25000000000000000),
    (exactRationalLiteral (-153951903651) 312500000000000),
    (exactRationalLiteral 901095992559197 300000000000000000)
  ],
  ![
    (exactRationalLiteral 114093292178399 30000000000000000),
    (exactRationalLiteral (-118927818122653) 50000000000000000),
    (exactRationalLiteral (-375689755219) 10000000000000000),
    (exactRationalLiteral 44999329483 18750000000000000)
  ],
  ![
    (exactRationalLiteral 5136207043457411 300000000000000000),
    (exactRationalLiteral (-802576835068541) 100000000000000000),
    (exactRationalLiteral 1539663760981 800000000000000),
    (exactRationalLiteral (-5481000175213) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-346397826709039) 50000000000000000),
    (exactRationalLiteral 23657475480997 5000000000000000),
    (exactRationalLiteral (-24611628946803) 10000000000000000),
    (exactRationalLiteral 58459359041369 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-688422524058869) 60000000000000000),
    (exactRationalLiteral 87872791230483 20000000000000000),
    (exactRationalLiteral (-10614277351603) 100000000000000000),
    (exactRationalLiteral (-4764673929751) 10000000000000000)
  ],
  ![
    (exactRationalLiteral (-12528792463971) 4000000000000000),
    (exactRationalLiteral 124682182861589 100000000000000000),
    (exactRationalLiteral (-98914839184869) 100000000000000000),
    (exactRationalLiteral 91615885062439 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-2027182099970203) 37500000000000000),
    (exactRationalLiteral 557772857198549 25000000000000000),
    (exactRationalLiteral (-116391297195923) 25000000000000000),
    (exactRationalLiteral 4886302371379 30000000000000000)
  ],
  ![
    (exactRationalLiteral 8218774187769253 75000000000000000),
    (exactRationalLiteral (-615268076785613) 12500000000000000),
    (exactRationalLiteral 282431686574623 25000000000000000),
    (exactRationalLiteral (-158671603203763) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-2027182099970203) 37500000000000000),
    (exactRationalLiteral 557772857198549 25000000000000000),
    (exactRationalLiteral (-116391297195923) 25000000000000000),
    (exactRationalLiteral 4886302371379 30000000000000000)
  ],
  ![
    (exactRationalLiteral (-12528792463971) 4000000000000000),
    (exactRationalLiteral 124682182861589 100000000000000000),
    (exactRationalLiteral (-98914839184869) 100000000000000000),
    (exactRationalLiteral 91615885062439 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-688422524058869) 60000000000000000),
    (exactRationalLiteral 87872791230483 20000000000000000),
    (exactRationalLiteral (-10614277351603) 100000000000000000),
    (exactRationalLiteral (-4764673929751) 10000000000000000)
  ],
  ![
    (exactRationalLiteral (-346397826709039) 50000000000000000),
    (exactRationalLiteral 23657475480997 5000000000000000),
    (exactRationalLiteral (-24611628946803) 10000000000000000),
    (exactRationalLiteral 58459359041369 75000000000000000)
  ],
  ![
    (exactRationalLiteral 5136207043457411 300000000000000000),
    (exactRationalLiteral (-802576835068541) 100000000000000000),
    (exactRationalLiteral 1539663760981 800000000000000),
    (exactRationalLiteral (-5481000175213) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 114093292178399 30000000000000000),
    (exactRationalLiteral (-118927818122653) 50000000000000000),
    (exactRationalLiteral (-375689755219) 10000000000000000),
    (exactRationalLiteral 44999329483 18750000000000000)
  ],
  ![
    (exactRationalLiteral (-126635444208193) 25000000000000000),
    (exactRationalLiteral (-230979192739713) 25000000000000000),
    (exactRationalLiteral (-153951903651) 312500000000000),
    (exactRationalLiteral 901095992559197 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1263412987075841) 100000000000000000),
    (exactRationalLiteral (-4233860237219353) 100000000000000000),
    (exactRationalLiteral (-5309177339557491) 100000000000000000),
    (exactRationalLiteral 4333771823778993 100000000000000000)
  ],
  ![
    (exactRationalLiteral 1994257532342653 15000000000000000),
    (exactRationalLiteral 12357607114657751 50000000000000000),
    (exactRationalLiteral 10436920042575493 50000000000000000),
    (exactRationalLiteral (-15910306462989143) 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-48257181212427683) 300000000000000000),
    (exactRationalLiteral (-31935545779784453) 100000000000000000),
    (exactRationalLiteral (-5296247425755397) 20000000000000000),
    (exactRationalLiteral 53699376594889417 100000000000000000)
  ],
  ![
    (exactRationalLiteral 518465601045967 100000000000000000),
    (exactRationalLiteral 2113110188559867 20000000000000000),
    (exactRationalLiteral 10818255858724131 100000000000000000),
    (exactRationalLiteral (-154244935466861561) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 3108507832971327 100000000000000000),
    (exactRationalLiteral 3117850316586273 100000000000000000),
    (exactRationalLiteral 2052177064116693 100000000000000000),
    (exactRationalLiteral 4404803472473617 18750000000000000)
  ],
  ![
    (exactRationalLiteral 2395356213600193 300000000000000000),
    (exactRationalLiteral (-2977296515391551) 100000000000000000),
    (exactRationalLiteral (-5110452385629149) 100000000000000000),
    (exactRationalLiteral (-563266099067809) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-1923841112364749) 300000000000000000),
    (exactRationalLiteral 7668963147722809 100000000000000000),
    (exactRationalLiteral 14258829184554421 100000000000000000),
    (exactRationalLiteral (-2127089624263657) 18750000000000000)
  ],
  ![
    (exactRationalLiteral 23000615866913531 300000000000000000),
    (exactRationalLiteral (-6256052581773907) 100000000000000000),
    (exactRationalLiteral (-28650786931603939) 100000000000000000),
    (exactRationalLiteral 26945036698976473 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-28643959928971939) 300000000000000000),
    (exactRationalLiteral (-5832384768028787) 100000000000000000),
    (exactRationalLiteral 31120371423099713 100000000000000000),
    (exactRationalLiteral (-46447636186158697) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 4156971898594297 300000000000000000),
    (exactRationalLiteral 10103454809566511 100000000000000000),
    (exactRationalLiteral (-3446733632729383) 20000000000000000),
    (exactRationalLiteral 20798774840687117 300000000000000000)
  ],
  ![
    (exactRationalLiteral 472344886475671 37500000000000000),
    (exactRationalLiteral (-472344886475671) 12500000000000000),
    (exactRationalLiteral 472344886475671 12500000000000000),
    (exactRationalLiteral (-472344886475671) 37500000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix9_eq :
    normalizedGeneratorCellMatrix9 = generatorCellMatrix9 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix9 j a = generatorCellMatrix9 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 10. -/
def normalizedGeneratorCellMatrix10 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral 594184446173367 50000000000000000),
    (exactRationalLiteral (-1782553338520101) 50000000000000000),
    (exactRationalLiteral 1782553338520101 50000000000000000),
    (exactRationalLiteral (-594184446173367) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 386181925041071 150000000000000000),
    (exactRationalLiteral 4980360946005971 50000000000000000),
    (exactRationalLiteral (-1915908095382373) 12500000000000000),
    (exactRationalLiteral 3602107239716501 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-27829829275267061) 300000000000000000),
    (exactRationalLiteral (-9667553047028839) 100000000000000000),
    (exactRationalLiteral 25239286466349007 100000000000000000),
    (exactRationalLiteral (-10655389087355499) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 9942033965416143 100000000000000000),
    (exactRationalLiteral 2153187528613139 100000000000000000),
    (exactRationalLiteral (-19774604803664091) 100000000000000000),
    (exactRationalLiteral 641786061378919 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-8040318295244381) 100000000000000000),
    (exactRationalLiteral (-3090253136584217) 20000000000000000),
    (exactRationalLiteral (-1472703356380077) 20000000000000000),
    (exactRationalLiteral 6924735531382707 25000000000000000)
  ],
  ![
    (exactRationalLiteral 95312461200600751 300000000000000000),
    (exactRationalLiteral 77699060004397531 100000000000000000),
    (exactRationalLiteral 14505806524738913 20000000000000000),
    (exactRationalLiteral (-36259129574712431) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-44269059129576631) 150000000000000000),
    (exactRationalLiteral (-30510718201653491) 25000000000000000),
    (exactRationalLiteral (-14342667960813743) 10000000000000000),
    (exactRationalLiteral 86105227644208241 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-31204700076721873) 150000000000000000),
    (exactRationalLiteral 19050027436832457 25000000000000000),
    (exactRationalLiteral 67308446327945633 50000000000000000),
    (exactRationalLiteral (-52837363510600257) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 97100781275306809 300000000000000000),
    (exactRationalLiteral (-13088637915328241) 100000000000000000),
    (exactRationalLiteral (-58677692229794729) 100000000000000000),
    (exactRationalLiteral 105787915665663187 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1618169685018423) 25000000000000000),
    (exactRationalLiteral (-462724861249339) 25000000000000000),
    (exactRationalLiteral 240379316618109 3125000000000000),
    (exactRationalLiteral (-617314191356611) 20000000000000000)
  ],
  ![
    (exactRationalLiteral (-707614695664127) 60000000000000000),
    (exactRationalLiteral (-24269999347259) 20000000000000000),
    (exactRationalLiteral 851831383390877 100000000000000000),
    (exactRationalLiteral (-537836991451313) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 13893843655441 10000000000000000),
    (exactRationalLiteral (-122324721038979) 50000000000000000),
    (exactRationalLiteral (-1518454140231) 50000000000000000),
    (exactRationalLiteral 38007805070467 50000000000000000)
  ],
  ![
    (exactRationalLiteral 3283926447918811 300000000000000000),
    (exactRationalLiteral (-439584895524143) 100000000000000000),
    (exactRationalLiteral 170533969421773 100000000000000000),
    (exactRationalLiteral (-128250778905511) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-290862465908257) 75000000000000000),
    (exactRationalLiteral 53688591712339 25000000000000000),
    (exactRationalLiteral (-6139426651277) 50000000000000000),
    (exactRationalLiteral (-32689520115149) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-2298803801784439) 300000000000000000),
    (exactRationalLiteral 275195183556679 100000000000000000),
    (exactRationalLiteral (-153554495244133) 100000000000000000),
    (exactRationalLiteral 71704592532279 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-679125633642787) 300000000000000000),
    (exactRationalLiteral 110084274616729 100000000000000000),
    (exactRationalLiteral 84316930940009 100000000000000000),
    (exactRationalLiteral (-97120485307423) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-5436007528008161) 150000000000000000),
    (exactRationalLiteral 674412037470301 50000000000000000),
    (exactRationalLiteral (-208351082534951) 50000000000000000),
    (exactRationalLiteral 115208718609889 100000000000000000)
  ],
  ![
    (exactRationalLiteral 84721999762841 1200000000000000),
    (exactRationalLiteral (-1490017164047723) 50000000000000000),
    (exactRationalLiteral 406191769945483 50000000000000000),
    (exactRationalLiteral (-680519415137) 390625000000000)
  ],
  ![
    (exactRationalLiteral (-5436007528008161) 150000000000000000),
    (exactRationalLiteral 674412037470301 50000000000000000),
    (exactRationalLiteral (-208351082534951) 50000000000000000),
    (exactRationalLiteral 115208718609889 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-679125633642787) 300000000000000000),
    (exactRationalLiteral 110084274616729 100000000000000000),
    (exactRationalLiteral 84316930940009 100000000000000000),
    (exactRationalLiteral (-97120485307423) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-2298803801784439) 300000000000000000),
    (exactRationalLiteral 275195183556679 100000000000000000),
    (exactRationalLiteral (-153554495244133) 100000000000000000),
    (exactRationalLiteral 71704592532279 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-290862465908257) 75000000000000000),
    (exactRationalLiteral 53688591712339 25000000000000000),
    (exactRationalLiteral (-6139426651277) 50000000000000000),
    (exactRationalLiteral (-32689520115149) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 3283926447918811 300000000000000000),
    (exactRationalLiteral (-439584895524143) 100000000000000000),
    (exactRationalLiteral 170533969421773 100000000000000000),
    (exactRationalLiteral (-128250778905511) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 13893843655441 10000000000000000),
    (exactRationalLiteral (-122324721038979) 50000000000000000),
    (exactRationalLiteral (-1518454140231) 50000000000000000),
    (exactRationalLiteral 38007805070467 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-707614695664127) 60000000000000000),
    (exactRationalLiteral (-24269999347259) 20000000000000000),
    (exactRationalLiteral 851831383390877 100000000000000000),
    (exactRationalLiteral (-537836991451313) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1618169685018423) 25000000000000000),
    (exactRationalLiteral (-462724861249339) 25000000000000000),
    (exactRationalLiteral 240379316618109 3125000000000000),
    (exactRationalLiteral (-617314191356611) 20000000000000000)
  ],
  ![
    (exactRationalLiteral 97100781275306809 300000000000000000),
    (exactRationalLiteral (-13088637915328241) 100000000000000000),
    (exactRationalLiteral (-58677692229794729) 100000000000000000),
    (exactRationalLiteral 105787915665663187 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-31204700076721873) 150000000000000000),
    (exactRationalLiteral 19050027436832457 25000000000000000),
    (exactRationalLiteral 67308446327945633 50000000000000000),
    (exactRationalLiteral (-52837363510600257) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-44269059129576631) 150000000000000000),
    (exactRationalLiteral (-30510718201653491) 25000000000000000),
    (exactRationalLiteral (-14342667960813743) 10000000000000000),
    (exactRationalLiteral 86105227644208241 60000000000000000)
  ],
  ![
    (exactRationalLiteral 95312461200600751 300000000000000000),
    (exactRationalLiteral 77699060004397531 100000000000000000),
    (exactRationalLiteral 14505806524738913 20000000000000000),
    (exactRationalLiteral (-36259129574712431) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-8040318295244381) 100000000000000000),
    (exactRationalLiteral (-3090253136584217) 20000000000000000),
    (exactRationalLiteral (-1472703356380077) 20000000000000000),
    (exactRationalLiteral 6924735531382707 25000000000000000)
  ],
  ![
    (exactRationalLiteral 9942033965416143 100000000000000000),
    (exactRationalLiteral 2153187528613139 100000000000000000),
    (exactRationalLiteral (-19774604803664091) 100000000000000000),
    (exactRationalLiteral 641786061378919 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-27829829275267061) 300000000000000000),
    (exactRationalLiteral (-9667553047028839) 100000000000000000),
    (exactRationalLiteral 25239286466349007 100000000000000000),
    (exactRationalLiteral (-10655389087355499) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 386181925041071 150000000000000000),
    (exactRationalLiteral 4980360946005971 50000000000000000),
    (exactRationalLiteral (-1915908095382373) 12500000000000000),
    (exactRationalLiteral 3602107239716501 60000000000000000)
  ],
  ![
    (exactRationalLiteral 594184446173367 50000000000000000),
    (exactRationalLiteral (-1782553338520101) 50000000000000000),
    (exactRationalLiteral 1782553338520101 50000000000000000),
    (exactRationalLiteral (-594184446173367) 50000000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix10_eq :
    normalizedGeneratorCellMatrix10 = generatorCellMatrix10 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix10 j a = generatorCellMatrix10 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 11. -/
def normalizedGeneratorCellMatrix11 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral 2683271435523521 300000000000000000),
    (exactRationalLiteral (-2683271435523521) 100000000000000000),
    (exactRationalLiteral 2683271435523521 100000000000000000),
    (exactRationalLiteral (-2683271435523521) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-6540398139686527) 150000000000000000),
    (exactRationalLiteral 4422426311801339 50000000000000000),
    (exactRationalLiteral (-672688079571749) 10000000000000000),
    (exactRationalLiteral 354243430110931 18750000000000000)
  ],
  ![
    (exactRationalLiteral (-2545094818603457) 100000000000000000),
    (exactRationalLiteral (-21993156605620987) 100000000000000000),
    (exactRationalLiteral (-874347866114007) 20000000000000000),
    (exactRationalLiteral 31280559454301113 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-3156158634535023) 100000000000000000),
    (exactRationalLiteral 52918527129870629 100000000000000000),
    (exactRationalLiteral 75733309594692099 100000000000000000),
    (exactRationalLiteral (-63747944883382631) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 85307900829059197 100000000000000000),
    (exactRationalLiteral (-67315911345912787) 100000000000000000),
    (exactRationalLiteral (-217544003974004883) 100000000000000000),
    (exactRationalLiteral 17900700485749469 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-454420637282366239) 300000000000000000),
    (exactRationalLiteral 21629906198152381 100000000000000000),
    (exactRationalLiteral 11483978344516151 4000000000000000),
    (exactRationalLiteral (-160577414132309651) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 126508712996308997 150000000000000000),
    (exactRationalLiteral 14204856997755409 50000000000000000),
    (exactRationalLiteral (-45601822101927569) 25000000000000000),
    (exactRationalLiteral 11156120526012551 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-6205146747199457) 150000000000000000),
    (exactRationalLiteral (-1541006669328407) 6250000000000000),
    (exactRationalLiteral 23555111717934229 50000000000000000),
    (exactRationalLiteral (-14700023990103469) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-743602202014923) 20000000000000000),
    (exactRationalLiteral 854732789642491 20000000000000000),
    (exactRationalLiteral (-1567574738569677) 100000000000000000),
    (exactRationalLiteral 159447585874271 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-484460660251903) 60000000000000000),
    (exactRationalLiteral 506638787142833 100000000000000000),
    (exactRationalLiteral (-223842599511749) 100000000000000000),
    (exactRationalLiteral 311803547907067 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-8183075915769) 25000000000000000),
    (exactRationalLiteral (-283455352701) 1250000000000000),
    (exactRationalLiteral 11250496107117 5000000000000000),
    (exactRationalLiteral (-117737055118259) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 78284096356873 10000000000000000),
    (exactRationalLiteral (-56691933896527) 25000000000000000),
    (exactRationalLiteral 21141595258131 50000000000000000),
    (exactRationalLiteral 12454004845957 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-15535059080573) 7500000000000000),
    (exactRationalLiteral 2496352400279 2000000000000000),
    (exactRationalLiteral (-19414473383213) 25000000000000000),
    (exactRationalLiteral 89326323969223 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-429691989812491) 75000000000000000),
    (exactRationalLiteral 732799882661 400000000000000),
    (exactRationalLiteral 961863786761 1562500000000000),
    (exactRationalLiteral (-71055927472259) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-96720995862473) 100000000000000000),
    (exactRationalLiteral 84477165881901 100000000000000000),
    (exactRationalLiteral (-109924039674837) 100000000000000000),
    (exactRationalLiteral 26282128620067 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-1546004634114911) 60000000000000000),
    (exactRationalLiteral 172209180126093 20000000000000000),
    (exactRationalLiteral (-14215201848047) 20000000000000000),
    (exactRationalLiteral (-12656189922443) 37500000000000000)
  ],
  ![
    (exactRationalLiteral 7077454332635797 150000000000000000),
    (exactRationalLiteral (-187790615913873) 10000000000000000),
    (exactRationalLiteral 1158978516263 400000000000000),
    (exactRationalLiteral 13134130011673 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1546004634114911) 60000000000000000),
    (exactRationalLiteral 172209180126093 20000000000000000),
    (exactRationalLiteral (-14215201848047) 20000000000000000),
    (exactRationalLiteral (-12656189922443) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-96720995862473) 100000000000000000),
    (exactRationalLiteral 84477165881901 100000000000000000),
    (exactRationalLiteral (-109924039674837) 100000000000000000),
    (exactRationalLiteral 26282128620067 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-429691989812491) 75000000000000000),
    (exactRationalLiteral 732799882661 400000000000000),
    (exactRationalLiteral 961863786761 1562500000000000),
    (exactRationalLiteral (-71055927472259) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-15535059080573) 7500000000000000),
    (exactRationalLiteral 2496352400279 2000000000000000),
    (exactRationalLiteral (-19414473383213) 25000000000000000),
    (exactRationalLiteral 89326323969223 300000000000000000)
  ],
  ![
    (exactRationalLiteral 78284096356873 10000000000000000),
    (exactRationalLiteral (-56691933896527) 25000000000000000),
    (exactRationalLiteral 21141595258131 50000000000000000),
    (exactRationalLiteral 12454004845957 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-8183075915769) 25000000000000000),
    (exactRationalLiteral (-283455352701) 1250000000000000),
    (exactRationalLiteral 11250496107117 5000000000000000),
    (exactRationalLiteral (-117737055118259) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-484460660251903) 60000000000000000),
    (exactRationalLiteral 506638787142833 100000000000000000),
    (exactRationalLiteral (-223842599511749) 100000000000000000),
    (exactRationalLiteral 311803547907067 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-743602202014923) 20000000000000000),
    (exactRationalLiteral 854732789642491 20000000000000000),
    (exactRationalLiteral (-1567574738569677) 100000000000000000),
    (exactRationalLiteral 159447585874271 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-6205146747199457) 150000000000000000),
    (exactRationalLiteral (-1541006669328407) 6250000000000000),
    (exactRationalLiteral 23555111717934229 50000000000000000),
    (exactRationalLiteral (-14700023990103469) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 126508712996308997 150000000000000000),
    (exactRationalLiteral 14204856997755409 50000000000000000),
    (exactRationalLiteral (-45601822101927569) 25000000000000000),
    (exactRationalLiteral 11156120526012551 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-454420637282366239) 300000000000000000),
    (exactRationalLiteral 21629906198152381 100000000000000000),
    (exactRationalLiteral 11483978344516151 4000000000000000),
    (exactRationalLiteral (-160577414132309651) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 85307900829059197 100000000000000000),
    (exactRationalLiteral (-67315911345912787) 100000000000000000),
    (exactRationalLiteral (-217544003974004883) 100000000000000000),
    (exactRationalLiteral 17900700485749469 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-3156158634535023) 100000000000000000),
    (exactRationalLiteral 52918527129870629 100000000000000000),
    (exactRationalLiteral 75733309594692099 100000000000000000),
    (exactRationalLiteral (-63747944883382631) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-2545094818603457) 100000000000000000),
    (exactRationalLiteral (-21993156605620987) 100000000000000000),
    (exactRationalLiteral (-874347866114007) 20000000000000000),
    (exactRationalLiteral 31280559454301113 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-6540398139686527) 150000000000000000),
    (exactRationalLiteral 4422426311801339 50000000000000000),
    (exactRationalLiteral (-672688079571749) 10000000000000000),
    (exactRationalLiteral 354243430110931 18750000000000000)
  ],
  ![
    (exactRationalLiteral 2683271435523521 300000000000000000),
    (exactRationalLiteral (-2683271435523521) 100000000000000000),
    (exactRationalLiteral 2683271435523521 100000000000000000),
    (exactRationalLiteral (-2683271435523521) 300000000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix11_eq :
    normalizedGeneratorCellMatrix11 = generatorCellMatrix11 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix11 j a = generatorCellMatrix11 j a := by
    decide +kernel
  exact h k b

end PartialBalayage.Maximal.Square
