/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.ExactRationalLiteral
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix4
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix5
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix6
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix7

/-!
# Normalized exact generator-cell coefficient cache

Each directly reduced rational is checked by Lean's ordinary kernel, and the
whole finite table is identified with the already proved actual coefficients.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Directly reduced exact coefficient rows for actual generator cell 4. -/
def normalizedGeneratorCellMatrix4 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 684347342461457 75000000000000000),
    (exactRationalLiteral (-684347342461457) 25000000000000000),
    (exactRationalLiteral 684347342461457 25000000000000000),
    (exactRationalLiteral (-684347342461457) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 337250172175053 20000000000000000),
    (exactRationalLiteral 1428419404947729 20000000000000000),
    (exactRationalLiteral (-2648504365684173) 20000000000000000),
    (exactRationalLiteral 217236456403493 4000000000000000)
  ],
  ![
    (exactRationalLiteral (-22316672460431633) 300000000000000000),
    (exactRationalLiteral (-2661763951850207) 100000000000000000),
    (exactRationalLiteral 25284660252933973 100000000000000000),
    (exactRationalLiteral (-6662333516965023) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 5240278380610517 100000000000000000),
    (exactRationalLiteral (-6940754823571749) 100000000000000000),
    (exactRationalLiteral (-23948738863632921) 100000000000000000),
    (exactRationalLiteral 3241220023163357 18750000000000000)
  ],
  ![
    (exactRationalLiteral 11241802657859 300000000000000000),
    (exactRationalLiteral 7062642102420883 100000000000000000),
    (exactRationalLiteral 2338922622865399 20000000000000000),
    (exactRationalLiteral (-19020154938621331) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-35230512528983) 9375000000000000),
    (exactRationalLiteral (-106365614267877) 5000000000000000),
    (exactRationalLiteral (-190260593526937) 6250000000000000),
    (exactRationalLiteral 7961430203784037 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-3138380096629) 10000000000000000),
    (exactRationalLiteral 199834536485503 50000000000000000),
    (exactRationalLiteral 337633951529151 50000000000000000),
    (exactRationalLiteral (-507447996555683) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-184571873811847) 300000000000000000),
    (exactRationalLiteral (-117023493609243) 100000000000000000),
    (exactRationalLiteral (-183939058576651) 100000000000000000),
    (exactRationalLiteral 310326759442987 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-71505212116231) 150000000000000000),
    (exactRationalLiteral 756195341973 5000000000000000),
    (exactRationalLiteral 22440811786793 50000000000000000),
    (exactRationalLiteral (-87290958933071) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 5479273462559 100000000000000000),
    (exactRationalLiteral 6798501892211 100000000000000000),
    (exactRationalLiteral (-9392473443429) 100000000000000000),
    (exactRationalLiteral 84276138601183 300000000000000000)
  ],
  ![
    (exactRationalLiteral 449511467142049 300000000000000000),
    (exactRationalLiteral 16085441253287 20000000000000000),
    (exactRationalLiteral 752622144689 20000000000000000),
    (exactRationalLiteral (-12787489951133) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 5742821714749 100000000000000000),
    (exactRationalLiteral 1833025254197 4000000000000000),
    (exactRationalLiteral 60612090633003 100000000000000000),
    (exactRationalLiteral (-843109872557) 30000000000000000)
  ],
  ![
    (exactRationalLiteral (-1332197244393799) 150000000000000000),
    (exactRationalLiteral (-4964154155779) 10000000000000000),
    (exactRationalLiteral (-39930863917123) 50000000000000000),
    (exactRationalLiteral (-1917384649293) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-126526661310991) 25000000000000000),
    (exactRationalLiteral 2068317301049 25000000000000000),
    (exactRationalLiteral 49628730946857 50000000000000000),
    (exactRationalLiteral (-124519941739099) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-788834707573199) 150000000000000000),
    (exactRationalLiteral 93241669864663 25000000000000000),
    (exactRationalLiteral 271019029193 250000000000000),
    (exactRationalLiteral (-160610961020153) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1172213534202457) 60000000000000000),
    (exactRationalLiteral 493752470340003 100000000000000000),
    (exactRationalLiteral 561294113368957 100000000000000000),
    (exactRationalLiteral (-701233095067877) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-9761638465549931) 150000000000000000),
    (exactRationalLiteral 256393578384159 25000000000000000),
    (exactRationalLiteral 273070708170383 10000000000000000),
    (exactRationalLiteral (-3067884871681387) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-59469529605834751) 150000000000000000),
    (exactRationalLiteral 6521610897170129 50000000000000000),
    (exactRationalLiteral 27225221178822893 50000000000000000),
    (exactRationalLiteral (-9173105315339653) 30000000000000000)
  ],
  ![
    (exactRationalLiteral 59264535527176621 30000000000000000),
    (exactRationalLiteral 8091555159598499 12500000000000000),
    (exactRationalLiteral (-178817390134348333) 50000000000000000),
    (exactRationalLiteral 3883154726554991 2343750000000000)
  ],
  ![
    (exactRationalLiteral (-164416774939500601) 100000000000000000),
    (exactRationalLiteral (-377653805610230583) 100000000000000000),
    (exactRationalLiteral 762917784164011401 100000000000000000),
    (exactRationalLiteral (-943315869997014223) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-26181459929894569) 50000000000000000),
    (exactRationalLiteral 5511268894092231 1000000000000000),
    (exactRationalLiteral (-93093949851628749) 12500000000000000),
    (exactRationalLiteral 419449777751426773 150000000000000000)
  ],
  ![
    (exactRationalLiteral 288142657123183861 300000000000000000),
    (exactRationalLiteral (-331474391063983929) 100000000000000000),
    (exactRationalLiteral 355587842410088137 100000000000000000),
    (exactRationalLiteral (-92123242491418831) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-404348209762868497) 300000000000000000),
    (exactRationalLiteral 184071540370475697 100000000000000000),
    (exactRationalLiteral (-135256936504126291) 100000000000000000),
    (exactRationalLiteral 120098771356237997 300000000000000000)
  ],
  ![
    (exactRationalLiteral 161918727665951221 75000000000000000),
    (exactRationalLiteral (-10586516088984323) 5000000000000000),
    (exactRationalLiteral 7649377046088487 6250000000000000),
    (exactRationalLiteral (-24204094702683523) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-404348209762868497) 300000000000000000),
    (exactRationalLiteral 184071540370475697 100000000000000000),
    (exactRationalLiteral (-135256936504126291) 100000000000000000),
    (exactRationalLiteral 120098771356237997 300000000000000000)
  ],
  ![
    (exactRationalLiteral 288142657123183861 300000000000000000),
    (exactRationalLiteral (-331474391063983929) 100000000000000000),
    (exactRationalLiteral 355587842410088137 100000000000000000),
    (exactRationalLiteral (-92123242491418831) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-26181459929894569) 50000000000000000),
    (exactRationalLiteral 5511268894092231 1000000000000000),
    (exactRationalLiteral (-93093949851628749) 12500000000000000),
    (exactRationalLiteral 419449777751426773 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-164416774939500601) 100000000000000000),
    (exactRationalLiteral (-377653805610230583) 100000000000000000),
    (exactRationalLiteral 762917784164011401 100000000000000000),
    (exactRationalLiteral (-943315869997014223) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 59264535527176621 30000000000000000),
    (exactRationalLiteral 8091555159598499 12500000000000000),
    (exactRationalLiteral (-178817390134348333) 50000000000000000),
    (exactRationalLiteral 3883154726554991 2343750000000000)
  ],
  ![
    (exactRationalLiteral (-59469529605834751) 150000000000000000),
    (exactRationalLiteral 6521610897170129 50000000000000000),
    (exactRationalLiteral 27225221178822893 50000000000000000),
    (exactRationalLiteral (-9173105315339653) 30000000000000000)
  ],
  ![
    (exactRationalLiteral (-9761638465549931) 150000000000000000),
    (exactRationalLiteral 256393578384159 25000000000000000),
    (exactRationalLiteral 273070708170383 10000000000000000),
    (exactRationalLiteral (-3067884871681387) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1172213534202457) 60000000000000000),
    (exactRationalLiteral 493752470340003 100000000000000000),
    (exactRationalLiteral 561294113368957 100000000000000000),
    (exactRationalLiteral (-701233095067877) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-788834707573199) 150000000000000000),
    (exactRationalLiteral 93241669864663 25000000000000000),
    (exactRationalLiteral 271019029193 250000000000000),
    (exactRationalLiteral (-160610961020153) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-126526661310991) 25000000000000000),
    (exactRationalLiteral 2068317301049 25000000000000000),
    (exactRationalLiteral 49628730946857 50000000000000000),
    (exactRationalLiteral (-124519941739099) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1332197244393799) 150000000000000000),
    (exactRationalLiteral (-4964154155779) 10000000000000000),
    (exactRationalLiteral (-39930863917123) 50000000000000000),
    (exactRationalLiteral (-1917384649293) 25000000000000000)
  ],
  ![
    (exactRationalLiteral 5742821714749 100000000000000000),
    (exactRationalLiteral 1833025254197 4000000000000000),
    (exactRationalLiteral 60612090633003 100000000000000000),
    (exactRationalLiteral (-843109872557) 30000000000000000)
  ],
  ![
    (exactRationalLiteral 449511467142049 300000000000000000),
    (exactRationalLiteral 16085441253287 20000000000000000),
    (exactRationalLiteral 752622144689 20000000000000000),
    (exactRationalLiteral (-12787489951133) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 5479273462559 100000000000000000),
    (exactRationalLiteral 6798501892211 100000000000000000),
    (exactRationalLiteral (-9392473443429) 100000000000000000),
    (exactRationalLiteral 84276138601183 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-71505212116231) 150000000000000000),
    (exactRationalLiteral 756195341973 5000000000000000),
    (exactRationalLiteral 22440811786793 50000000000000000),
    (exactRationalLiteral (-87290958933071) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-184571873811847) 300000000000000000),
    (exactRationalLiteral (-117023493609243) 100000000000000000),
    (exactRationalLiteral (-183939058576651) 100000000000000000),
    (exactRationalLiteral 310326759442987 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-3138380096629) 10000000000000000),
    (exactRationalLiteral 199834536485503 50000000000000000),
    (exactRationalLiteral 337633951529151 50000000000000000),
    (exactRationalLiteral (-507447996555683) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-35230512528983) 9375000000000000),
    (exactRationalLiteral (-106365614267877) 5000000000000000),
    (exactRationalLiteral (-190260593526937) 6250000000000000),
    (exactRationalLiteral 7961430203784037 150000000000000000)
  ],
  ![
    (exactRationalLiteral 11241802657859 300000000000000000),
    (exactRationalLiteral 7062642102420883 100000000000000000),
    (exactRationalLiteral 2338922622865399 20000000000000000),
    (exactRationalLiteral (-19020154938621331) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 5240278380610517 100000000000000000),
    (exactRationalLiteral (-6940754823571749) 100000000000000000),
    (exactRationalLiteral (-23948738863632921) 100000000000000000),
    (exactRationalLiteral 3241220023163357 18750000000000000)
  ],
  ![
    (exactRationalLiteral (-22316672460431633) 300000000000000000),
    (exactRationalLiteral (-2661763951850207) 100000000000000000),
    (exactRationalLiteral 25284660252933973 100000000000000000),
    (exactRationalLiteral (-6662333516965023) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 337250172175053 20000000000000000),
    (exactRationalLiteral 1428419404947729 20000000000000000),
    (exactRationalLiteral (-2648504365684173) 20000000000000000),
    (exactRationalLiteral 217236456403493 4000000000000000)
  ],
  ![
    (exactRationalLiteral 684347342461457 75000000000000000),
    (exactRationalLiteral (-684347342461457) 25000000000000000),
    (exactRationalLiteral 684347342461457 25000000000000000),
    (exactRationalLiteral (-684347342461457) 75000000000000000)
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
theorem normalizedGeneratorCellMatrix4_eq :
    normalizedGeneratorCellMatrix4 = generatorCellMatrix4 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix4 j a = generatorCellMatrix4 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 5. -/
def normalizedGeneratorCellMatrix5 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 101673746728037 10000000000000000),
    (exactRationalLiteral (-305021240184111) 10000000000000000),
    (exactRationalLiteral 305021240184111 10000000000000000),
    (exactRationalLiteral (-101673746728037) 10000000000000000)
  ],
  ![
    (exactRationalLiteral 5578015341029527 300000000000000000),
    (exactRationalLiteral 7933555452227601 100000000000000000),
    (exactRationalLiteral (-2937868169771233) 20000000000000000),
    (exactRationalLiteral 6022411182390149 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-25088125549168747) 300000000000000000),
    (exactRationalLiteral (-2978712180223879) 100000000000000000),
    (exactRationalLiteral 27910781506980791 100000000000000000),
    (exactRationalLiteral (-733494994295213) 5000000000000000)
  ],
  ![
    (exactRationalLiteral 6080899191886277 100000000000000000),
    (exactRationalLiteral (-7588441546167789) 100000000000000000),
    (exactRationalLiteral (-26345696762915667) 100000000000000000),
    (exactRationalLiteral 754836833325719 4000000000000000)
  ],
  ![
    (exactRationalLiteral (-359480669362489) 150000000000000000),
    (exactRationalLiteral 154144182586971 2000000000000000),
    (exactRationalLiteral 6439345455568541 50000000000000000),
    (exactRationalLiteral (-10278710464759649) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-92892444725641) 30000000000000000),
    (exactRationalLiteral (-1154689546678927) 50000000000000000),
    (exactRationalLiteral (-1692158034693581) 50000000000000000),
    (exactRationalLiteral 2121624828238697 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-19559906505071) 37500000000000000),
    (exactRationalLiteral 27879916722901 6250000000000000),
    (exactRationalLiteral 74704121975231 10000000000000000),
    (exactRationalLiteral (-2132147984069059) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-224866709792537) 300000000000000000),
    (exactRationalLiteral (-156985722812581) 100000000000000000),
    (exactRationalLiteral (-216991253225627) 100000000000000000),
    (exactRationalLiteral 347168369735637 100000000000000000)
  ],
  ![
    (exactRationalLiteral 46466022167603 150000000000000000),
    (exactRationalLiteral 9036211700817 12500000000000000),
    (exactRationalLiteral 37441832578877 50000000000000000),
    (exactRationalLiteral (-120536874772229) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 225502479403141 100000000000000000),
    (exactRationalLiteral 62378447811059 100000000000000000),
    (exactRationalLiteral (-21811869178821) 100000000000000000),
    (exactRationalLiteral 184532379002761 300000000000000000)
  ],
  ![
    (exactRationalLiteral 328110532382461 300000000000000000),
    (exactRationalLiteral 158618713895361 100000000000000000),
    (exactRationalLiteral 52180991907433 100000000000000000),
    (exactRationalLiteral (-53808752947261) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1537956456377611) 150000000000000000),
    (exactRationalLiteral (-116186806508899) 50000000000000000),
    (exactRationalLiteral (-51435171812881) 50000000000000000),
    (exactRationalLiteral 7356010497497 18750000000000000)
  ],
  ![
    (exactRationalLiteral (-1320247684177261) 300000000000000000),
    (exactRationalLiteral 3290730050101 4000000000000000),
    (exactRationalLiteral (-5052495969077) 20000000000000000),
    (exactRationalLiteral (-115423359971879) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-19610500183933) 20000000000000000),
    (exactRationalLiteral 429170941792899 100000000000000000),
    (exactRationalLiteral (-52203349342953) 100000000000000000),
    (exactRationalLiteral 62182460934331 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1698580507476641) 150000000000000000),
    (exactRationalLiteral 22877690050251 2500000000000000),
    (exactRationalLiteral (-3498474542473) 2500000000000000),
    (exactRationalLiteral 31995701020177 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-11322317617059851) 300000000000000000),
    (exactRationalLiteral 3419103605262909 100000000000000000),
    (exactRationalLiteral (-337177789977557) 100000000000000000),
    (exactRationalLiteral (-82513614126359) 20000000000000000)
  ],
  ![
    (exactRationalLiteral (-27297066363693) 1000000000000000),
    (exactRationalLiteral 302130533562353 1000000000000000),
    (exactRationalLiteral (-4660076349468843) 12500000000000000),
    (exactRationalLiteral 20150939630783831 150000000000000000)
  ],
  ![
    (exactRationalLiteral 52745535823769759 75000000000000000),
    (exactRationalLiteral (-38373328565391623) 25000000000000000),
    (exactRationalLiteral 69704512365171091 50000000000000000),
    (exactRationalLiteral (-11244603121287341) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-70193564788543393) 75000000000000000),
    (exactRationalLiteral 51216473180194499 25000000000000000),
    (exactRationalLiteral (-90199042916501411) 50000000000000000),
    (exactRationalLiteral 171082800113224387 300000000000000000)
  ],
  ![
    (exactRationalLiteral 6308541732004091 18750000000000000),
    (exactRationalLiteral (-49738376356991669) 50000000000000000),
    (exactRationalLiteral 47073978344911777 50000000000000000),
    (exactRationalLiteral (-7595311497034183) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-2669986268059613) 100000000000000000),
    (exactRationalLiteral 11208323790517021 100000000000000000),
    (exactRationalLiteral (-12905127555587187) 100000000000000000),
    (exactRationalLiteral 2697298680207731 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-68902813403791141) 150000000000000000),
    (exactRationalLiteral 4207054839807639 12500000000000000),
    (exactRationalLiteral (-7579082573944147) 50000000000000000),
    (exactRationalLiteral 10703400741920887 300000000000000000)
  ],
  ![
    (exactRationalLiteral 23569805393854899 25000000000000000),
    (exactRationalLiteral (-7970829389448621) 12500000000000000),
    (exactRationalLiteral 255736539266817 1000000000000000),
    (exactRationalLiteral (-1660770760339987) 30000000000000000)
  ],
  ![
    (exactRationalLiteral (-68902813403791141) 150000000000000000),
    (exactRationalLiteral 4207054839807639 12500000000000000),
    (exactRationalLiteral (-7579082573944147) 50000000000000000),
    (exactRationalLiteral 10703400741920887 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-2669986268059613) 100000000000000000),
    (exactRationalLiteral 11208323790517021 100000000000000000),
    (exactRationalLiteral (-12905127555587187) 100000000000000000),
    (exactRationalLiteral 2697298680207731 60000000000000000)
  ],
  ![
    (exactRationalLiteral 6308541732004091 18750000000000000),
    (exactRationalLiteral (-49738376356991669) 50000000000000000),
    (exactRationalLiteral 47073978344911777 50000000000000000),
    (exactRationalLiteral (-7595311497034183) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-70193564788543393) 75000000000000000),
    (exactRationalLiteral 51216473180194499 25000000000000000),
    (exactRationalLiteral (-90199042916501411) 50000000000000000),
    (exactRationalLiteral 171082800113224387 300000000000000000)
  ],
  ![
    (exactRationalLiteral 52745535823769759 75000000000000000),
    (exactRationalLiteral (-38373328565391623) 25000000000000000),
    (exactRationalLiteral 69704512365171091 50000000000000000),
    (exactRationalLiteral (-11244603121287341) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-27297066363693) 1000000000000000),
    (exactRationalLiteral 302130533562353 1000000000000000),
    (exactRationalLiteral (-4660076349468843) 12500000000000000),
    (exactRationalLiteral 20150939630783831 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-11322317617059851) 300000000000000000),
    (exactRationalLiteral 3419103605262909 100000000000000000),
    (exactRationalLiteral (-337177789977557) 100000000000000000),
    (exactRationalLiteral (-82513614126359) 20000000000000000)
  ],
  ![
    (exactRationalLiteral (-1698580507476641) 150000000000000000),
    (exactRationalLiteral 22877690050251 2500000000000000),
    (exactRationalLiteral (-3498474542473) 2500000000000000),
    (exactRationalLiteral 31995701020177 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-19610500183933) 20000000000000000),
    (exactRationalLiteral 429170941792899 100000000000000000),
    (exactRationalLiteral (-52203349342953) 100000000000000000),
    (exactRationalLiteral 62182460934331 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1320247684177261) 300000000000000000),
    (exactRationalLiteral 3290730050101 4000000000000000),
    (exactRationalLiteral (-5052495969077) 20000000000000000),
    (exactRationalLiteral (-115423359971879) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1537956456377611) 150000000000000000),
    (exactRationalLiteral (-116186806508899) 50000000000000000),
    (exactRationalLiteral (-51435171812881) 50000000000000000),
    (exactRationalLiteral 7356010497497 18750000000000000)
  ],
  ![
    (exactRationalLiteral 328110532382461 300000000000000000),
    (exactRationalLiteral 158618713895361 100000000000000000),
    (exactRationalLiteral 52180991907433 100000000000000000),
    (exactRationalLiteral (-53808752947261) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 225502479403141 100000000000000000),
    (exactRationalLiteral 62378447811059 100000000000000000),
    (exactRationalLiteral (-21811869178821) 100000000000000000),
    (exactRationalLiteral 184532379002761 300000000000000000)
  ],
  ![
    (exactRationalLiteral 46466022167603 150000000000000000),
    (exactRationalLiteral 9036211700817 12500000000000000),
    (exactRationalLiteral 37441832578877 50000000000000000),
    (exactRationalLiteral (-120536874772229) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-224866709792537) 300000000000000000),
    (exactRationalLiteral (-156985722812581) 100000000000000000),
    (exactRationalLiteral (-216991253225627) 100000000000000000),
    (exactRationalLiteral 347168369735637 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-19559906505071) 37500000000000000),
    (exactRationalLiteral 27879916722901 6250000000000000),
    (exactRationalLiteral 74704121975231 10000000000000000),
    (exactRationalLiteral (-2132147984069059) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-92892444725641) 30000000000000000),
    (exactRationalLiteral (-1154689546678927) 50000000000000000),
    (exactRationalLiteral (-1692158034693581) 50000000000000000),
    (exactRationalLiteral 2121624828238697 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-359480669362489) 150000000000000000),
    (exactRationalLiteral 154144182586971 2000000000000000),
    (exactRationalLiteral 6439345455568541 50000000000000000),
    (exactRationalLiteral (-10278710464759649) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 6080899191886277 100000000000000000),
    (exactRationalLiteral (-7588441546167789) 100000000000000000),
    (exactRationalLiteral (-26345696762915667) 100000000000000000),
    (exactRationalLiteral 754836833325719 4000000000000000)
  ],
  ![
    (exactRationalLiteral (-25088125549168747) 300000000000000000),
    (exactRationalLiteral (-2978712180223879) 100000000000000000),
    (exactRationalLiteral 27910781506980791 100000000000000000),
    (exactRationalLiteral (-733494994295213) 5000000000000000)
  ],
  ![
    (exactRationalLiteral 5578015341029527 300000000000000000),
    (exactRationalLiteral 7933555452227601 100000000000000000),
    (exactRationalLiteral (-2937868169771233) 20000000000000000),
    (exactRationalLiteral 6022411182390149 100000000000000000)
  ],
  ![
    (exactRationalLiteral 101673746728037 10000000000000000),
    (exactRationalLiteral (-305021240184111) 10000000000000000),
    (exactRationalLiteral 305021240184111 10000000000000000),
    (exactRationalLiteral (-101673746728037) 10000000000000000)
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
theorem normalizedGeneratorCellMatrix5_eq :
    normalizedGeneratorCellMatrix5 = generatorCellMatrix5 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix5 j a = generatorCellMatrix5 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 6. -/
def normalizedGeneratorCellMatrix6 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 1688946349157141 150000000000000000),
    (exactRationalLiteral (-1688946349157141) 50000000000000000),
    (exactRationalLiteral 1688946349157141 50000000000000000),
    (exactRationalLiteral (-1688946349157141) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 5698382773389209 300000000000000000),
    (exactRationalLiteral 8833151176024923 100000000000000000),
    (exactRationalLiteral (-16098918150731989) 100000000000000000),
    (exactRationalLiteral 3288633606347587 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-2245579571013551) 25000000000000000),
    (exactRationalLiteral (-1833536286285099) 50000000000000000),
    (exactRationalLiteral 15133532868256629 50000000000000000),
    (exactRationalLiteral (-47331388802343673) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 9961948461846661 150000000000000000),
    (exactRationalLiteral (-3825125453707941) 50000000000000000),
    (exactRationalLiteral (-14118075473950757) 50000000000000000),
    (exactRationalLiteral 7484329656219809 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-172835218263647) 50000000000000000),
    (exactRationalLiteral 3947493696888699 50000000000000000),
    (exactRationalLiteral 6794341278261207 50000000000000000),
    (exactRationalLiteral (-42738191672038021) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-70117963185209) 25000000000000000),
    (exactRationalLiteral (-1162067430533541) 50000000000000000),
    (exactRationalLiteral (-219828421774113) 6250000000000000),
    (exactRationalLiteral 2178540920378807 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-1221170114801) 1200000000000000),
    (exactRationalLiteral 112634219985769 25000000000000000),
    (exactRationalLiteral 206128463995321 25000000000000000),
    (exactRationalLiteral (-2250031784810413) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 172841496311389 300000000000000000),
    (exactRationalLiteral (-139553600394643) 100000000000000000),
    (exactRationalLiteral (-286726959158933) 100000000000000000),
    (exactRationalLiteral 1234234078396733 300000000000000000)
  ],
  ![
    (exactRationalLiteral 491369776554449 150000000000000000),
    (exactRationalLiteral 101643544228089 50000000000000000),
    (exactRationalLiteral 8136025491197 5000000000000000),
    (exactRationalLiteral (-481007783898793) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 852892143896321 300000000000000000),
    (exactRationalLiteral 31072638363141 20000000000000000),
    (exactRationalLiteral (-55436513987089) 100000000000000000),
    (exactRationalLiteral 120877376518999 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-26426324098173) 2000000000000000),
    (exactRationalLiteral (-32041813230937) 10000000000000000),
    (exactRationalLiteral 1482582433419 10000000000000000),
    (exactRationalLiteral (-463561827817627) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1380077089899599) 300000000000000000),
    (exactRationalLiteral (-199103428382003) 100000000000000000),
    (exactRationalLiteral (-256109199789143) 100000000000000000),
    (exactRationalLiteral (-879969698171) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 192222039291901 60000000000000000),
    (exactRationalLiteral 89825832995131 20000000000000000),
    (exactRationalLiteral 72161572525709 100000000000000000),
    (exactRationalLiteral 253127137092691 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-62978984498723) 18750000000000000),
    (exactRationalLiteral 349610520326277 50000000000000000),
    (exactRationalLiteral (-37973789829283) 50000000000000000),
    (exactRationalLiteral (-56378500616333) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-165712219154959) 15000000000000000),
    (exactRationalLiteral 150704381341241 10000000000000000),
    (exactRationalLiteral (-787441000936471) 50000000000000000),
    (exactRationalLiteral 708293293737149 100000000000000000)
  ],
  ![
    (exactRationalLiteral 1091008703391343 30000000000000000),
    (exactRationalLiteral (-2023144486849263) 50000000000000000),
    (exactRationalLiteral 1510634232908459 50000000000000000),
    (exactRationalLiteral (-500536674452579) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 16897018622979007 150000000000000000),
    (exactRationalLiteral (-480525112816511) 5000000000000000),
    (exactRationalLiteral 447378727489409 10000000000000000),
    (exactRationalLiteral (-29023050404839) 3000000000000000)
  ],
  ![
    (exactRationalLiteral (-12096012792541221) 100000000000000000),
    (exactRationalLiteral 15152521167996739 100000000000000000),
    (exactRationalLiteral (-1863057143955687) 20000000000000000),
    (exactRationalLiteral 146169954063853 6000000000000000)
  ],
  ![
    (exactRationalLiteral (-1548364581206023) 75000000000000000),
    (exactRationalLiteral (-1162288649373213) 50000000000000000),
    (exactRationalLiteral 1502109362706679 50000000000000000),
    (exactRationalLiteral (-2947819484283181) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 193061650824659 150000000000000000),
    (exactRationalLiteral (-557718959809349) 50000000000000000),
    (exactRationalLiteral 145341461362867 25000000000000000),
    (exactRationalLiteral (-22222996467439) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-71607405353942941) 300000000000000000),
    (exactRationalLiteral 14043509164605411 100000000000000000),
    (exactRationalLiteral (-4454764405967407) 100000000000000000),
    (exactRationalLiteral 1042241447353363 150000000000000000)
  ],
  ![
    (exactRationalLiteral 75825506778068557 150000000000000000),
    (exactRationalLiteral (-14613517432812719) 50000000000000000),
    (exactRationalLiteral 896594632328183 10000000000000000),
    (exactRationalLiteral (-694811939776553) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-71607405353942941) 300000000000000000),
    (exactRationalLiteral 14043509164605411 100000000000000000),
    (exactRationalLiteral (-4454764405967407) 100000000000000000),
    (exactRationalLiteral 1042241447353363 150000000000000000)
  ],
  ![
    (exactRationalLiteral 193061650824659 150000000000000000),
    (exactRationalLiteral (-557718959809349) 50000000000000000),
    (exactRationalLiteral 145341461362867 25000000000000000),
    (exactRationalLiteral (-22222996467439) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-1548364581206023) 75000000000000000),
    (exactRationalLiteral (-1162288649373213) 50000000000000000),
    (exactRationalLiteral 1502109362706679 50000000000000000),
    (exactRationalLiteral (-2947819484283181) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-12096012792541221) 100000000000000000),
    (exactRationalLiteral 15152521167996739 100000000000000000),
    (exactRationalLiteral (-1863057143955687) 20000000000000000),
    (exactRationalLiteral 146169954063853 6000000000000000)
  ],
  ![
    (exactRationalLiteral 16897018622979007 150000000000000000),
    (exactRationalLiteral (-480525112816511) 5000000000000000),
    (exactRationalLiteral 447378727489409 10000000000000000),
    (exactRationalLiteral (-29023050404839) 3000000000000000)
  ],
  ![
    (exactRationalLiteral 1091008703391343 30000000000000000),
    (exactRationalLiteral (-2023144486849263) 50000000000000000),
    (exactRationalLiteral 1510634232908459 50000000000000000),
    (exactRationalLiteral (-500536674452579) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-165712219154959) 15000000000000000),
    (exactRationalLiteral 150704381341241 10000000000000000),
    (exactRationalLiteral (-787441000936471) 50000000000000000),
    (exactRationalLiteral 708293293737149 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-62978984498723) 18750000000000000),
    (exactRationalLiteral 349610520326277 50000000000000000),
    (exactRationalLiteral (-37973789829283) 50000000000000000),
    (exactRationalLiteral (-56378500616333) 25000000000000000)
  ],
  ![
    (exactRationalLiteral 192222039291901 60000000000000000),
    (exactRationalLiteral 89825832995131 20000000000000000),
    (exactRationalLiteral 72161572525709 100000000000000000),
    (exactRationalLiteral 253127137092691 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1380077089899599) 300000000000000000),
    (exactRationalLiteral (-199103428382003) 100000000000000000),
    (exactRationalLiteral (-256109199789143) 100000000000000000),
    (exactRationalLiteral (-879969698171) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-26426324098173) 2000000000000000),
    (exactRationalLiteral (-32041813230937) 10000000000000000),
    (exactRationalLiteral 1482582433419 10000000000000000),
    (exactRationalLiteral (-463561827817627) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 852892143896321 300000000000000000),
    (exactRationalLiteral 31072638363141 20000000000000000),
    (exactRationalLiteral (-55436513987089) 100000000000000000),
    (exactRationalLiteral 120877376518999 75000000000000000)
  ],
  ![
    (exactRationalLiteral 491369776554449 150000000000000000),
    (exactRationalLiteral 101643544228089 50000000000000000),
    (exactRationalLiteral 8136025491197 5000000000000000),
    (exactRationalLiteral (-481007783898793) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 172841496311389 300000000000000000),
    (exactRationalLiteral (-139553600394643) 100000000000000000),
    (exactRationalLiteral (-286726959158933) 100000000000000000),
    (exactRationalLiteral 1234234078396733 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1221170114801) 1200000000000000),
    (exactRationalLiteral 112634219985769 25000000000000000),
    (exactRationalLiteral 206128463995321 25000000000000000),
    (exactRationalLiteral (-2250031784810413) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-70117963185209) 25000000000000000),
    (exactRationalLiteral (-1162067430533541) 50000000000000000),
    (exactRationalLiteral (-219828421774113) 6250000000000000),
    (exactRationalLiteral 2178540920378807 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-172835218263647) 50000000000000000),
    (exactRationalLiteral 3947493696888699 50000000000000000),
    (exactRationalLiteral 6794341278261207 50000000000000000),
    (exactRationalLiteral (-42738191672038021) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 9961948461846661 150000000000000000),
    (exactRationalLiteral (-3825125453707941) 50000000000000000),
    (exactRationalLiteral (-14118075473950757) 50000000000000000),
    (exactRationalLiteral 7484329656219809 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-2245579571013551) 25000000000000000),
    (exactRationalLiteral (-1833536286285099) 50000000000000000),
    (exactRationalLiteral 15133532868256629 50000000000000000),
    (exactRationalLiteral (-47331388802343673) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 5698382773389209 300000000000000000),
    (exactRationalLiteral 8833151176024923 100000000000000000),
    (exactRationalLiteral (-16098918150731989) 100000000000000000),
    (exactRationalLiteral 3288633606347587 50000000000000000)
  ],
  ![
    (exactRationalLiteral 1688946349157141 150000000000000000),
    (exactRationalLiteral (-1688946349157141) 50000000000000000),
    (exactRationalLiteral 1688946349157141 50000000000000000),
    (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
theorem normalizedGeneratorCellMatrix6_eq :
    normalizedGeneratorCellMatrix6 = generatorCellMatrix6 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix6 j a = generatorCellMatrix6 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 7. -/
def normalizedGeneratorCellMatrix7 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 3632883487353533 300000000000000000),
    (exactRationalLiteral (-3632883487353533) 100000000000000000),
    (exactRationalLiteral 3632883487353533 100000000000000000),
    (exactRationalLiteral (-3632883487353533) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1104327167464579 60000000000000000),
    (exactRationalLiteral 1907134019622529 20000000000000000),
    (exactRationalLiteral (-3412864613166083) 20000000000000000),
    (exactRationalLiteral 208286495496893 3000000000000000)
  ],
  ![
    (exactRationalLiteral (-4643445232083399) 50000000000000000),
    (exactRationalLiteral (-2123957776730219) 50000000000000000),
    (exactRationalLiteral 15819243150928479 50000000000000000),
    (exactRationalLiteral (-8185421794643431) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 20675806869279533 300000000000000000),
    (exactRationalLiteral (-1533167833043159) 20000000000000000),
    (exactRationalLiteral (-29149509115515607) 100000000000000000),
    (exactRationalLiteral 61225744742488021 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-468628511775361) 150000000000000000),
    (exactRationalLiteral 4034841502595879 50000000000000000),
    (exactRationalLiteral 1738884076830581 12500000000000000),
    (exactRationalLiteral (-43377828520127101) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-245050972636999) 75000000000000000),
    (exactRationalLiteral (-1200249488857591) 50000000000000000),
    (exactRationalLiteral (-1837774856819771) 50000000000000000),
    (exactRationalLiteral 223886765427899 3750000000000000)
  ],
  ![
    (exactRationalLiteral 21372316007899 50000000000000000),
    (exactRationalLiteral 4072082497533 781250000000000),
    (exactRationalLiteral 4737535596189 500000000000000),
    (exactRationalLiteral (-829467829519103) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 533251521350153 100000000000000000),
    (exactRationalLiteral 9544064841053 20000000000000000),
    (exactRationalLiteral (-318287274074853) 100000000000000000),
    (exactRationalLiteral 760074342064223 150000000000000000)
  ],
  ![
    (exactRationalLiteral 109078778897211 20000000000000000),
    (exactRationalLiteral 527999669917523 100000000000000000),
    (exactRationalLiteral 428072992088907 100000000000000000),
    (exactRationalLiteral (-93318174214333) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-5344287366469117) 300000000000000000),
    (exactRationalLiteral (-754328311458617) 100000000000000000),
    (exactRationalLiteral (-448736003483437) 100000000000000000),
    (exactRationalLiteral 461957851496033 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-2749234853205721) 300000000000000000),
    (exactRationalLiteral (-714841706752973) 100000000000000000),
    (exactRationalLiteral (-259629078581827) 100000000000000000),
    (exactRationalLiteral (-1980289854254507) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 3031236683148979 300000000000000000),
    (exactRationalLiteral 219941316842491 20000000000000000),
    (exactRationalLiteral 578415846711091 100000000000000000),
    (exactRationalLiteral 83868334984899 50000000000000000)
  ],
  ![
    (exactRationalLiteral 58004569877 93750000000000),
    (exactRationalLiteral (-64608063030287) 50000000000000000),
    (exactRationalLiteral (-376244793527281) 50000000000000000),
    (exactRationalLiteral 577000331593733 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-1392879067269329) 300000000000000000),
    (exactRationalLiteral 482159690877973 100000000000000000),
    (exactRationalLiteral 109999575867701 20000000000000000),
    (exactRationalLiteral (-150340274534201) 30000000000000000)
  ],
  ![
    (exactRationalLiteral 1207951365888283 75000000000000000),
    (exactRationalLiteral (-251743022195041) 25000000000000000),
    (exactRationalLiteral 4512104775361 25000000000000000),
    (exactRationalLiteral 59894007731893 50000000000000000)
  ],
  ![
    (exactRationalLiteral 3870396815291431 75000000000000000),
    (exactRationalLiteral (-178261637351297) 5000000000000000),
    (exactRationalLiteral 157148223441019 10000000000000000),
    (exactRationalLiteral (-178687396782983) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-11467834329776101) 300000000000000000),
    (exactRationalLiteral 3830447431632519 100000000000000000),
    (exactRationalLiteral (-401357603317157) 20000000000000000),
    (exactRationalLiteral 1454591208606403 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-7102353529106477) 300000000000000000),
    (exactRationalLiteral 736040667797109 100000000000000000),
    (exactRationalLiteral 56399241130177 100000000000000000),
    (exactRationalLiteral (-227630078841811) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-37069221961541) 7500000000000000),
    (exactRationalLiteral (-21938218632503) 10000000000000000),
    (exactRationalLiteral 1573449439211 500000000000000),
    (exactRationalLiteral (-62636306894389) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-40756688183322203) 300000000000000000),
    (exactRationalLiteral 7218463247377323 100000000000000000),
    (exactRationalLiteral (-2370281511260681) 100000000000000000),
    (exactRationalLiteral 161814868998913 37500000000000000)
  ],
  ![
    (exactRationalLiteral 21674719072611743 75000000000000000),
    (exactRationalLiteral (-1933001732215137) 12500000000000000),
    (exactRationalLiteral 299817167788907 6250000000000000),
    (exactRationalLiteral (-1244770389182459) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-40756688183322203) 300000000000000000),
    (exactRationalLiteral 7218463247377323 100000000000000000),
    (exactRationalLiteral (-2370281511260681) 100000000000000000),
    (exactRationalLiteral 161814868998913 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-37069221961541) 7500000000000000),
    (exactRationalLiteral (-21938218632503) 10000000000000000),
    (exactRationalLiteral 1573449439211 500000000000000),
    (exactRationalLiteral (-62636306894389) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-7102353529106477) 300000000000000000),
    (exactRationalLiteral 736040667797109 100000000000000000),
    (exactRationalLiteral 56399241130177 100000000000000000),
    (exactRationalLiteral (-227630078841811) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-11467834329776101) 300000000000000000),
    (exactRationalLiteral 3830447431632519 100000000000000000),
    (exactRationalLiteral (-401357603317157) 20000000000000000),
    (exactRationalLiteral 1454591208606403 300000000000000000)
  ],
  ![
    (exactRationalLiteral 3870396815291431 75000000000000000),
    (exactRationalLiteral (-178261637351297) 5000000000000000),
    (exactRationalLiteral 157148223441019 10000000000000000),
    (exactRationalLiteral (-178687396782983) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 1207951365888283 75000000000000000),
    (exactRationalLiteral (-251743022195041) 25000000000000000),
    (exactRationalLiteral 4512104775361 25000000000000000),
    (exactRationalLiteral 59894007731893 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-1392879067269329) 300000000000000000),
    (exactRationalLiteral 482159690877973 100000000000000000),
    (exactRationalLiteral 109999575867701 20000000000000000),
    (exactRationalLiteral (-150340274534201) 30000000000000000)
  ],
  ![
    (exactRationalLiteral 58004569877 93750000000000),
    (exactRationalLiteral (-64608063030287) 50000000000000000),
    (exactRationalLiteral (-376244793527281) 50000000000000000),
    (exactRationalLiteral 577000331593733 100000000000000000)
  ],
  ![
    (exactRationalLiteral 3031236683148979 300000000000000000),
    (exactRationalLiteral 219941316842491 20000000000000000),
    (exactRationalLiteral 578415846711091 100000000000000000),
    (exactRationalLiteral 83868334984899 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-2749234853205721) 300000000000000000),
    (exactRationalLiteral (-714841706752973) 100000000000000000),
    (exactRationalLiteral (-259629078581827) 100000000000000000),
    (exactRationalLiteral (-1980289854254507) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-5344287366469117) 300000000000000000),
    (exactRationalLiteral (-754328311458617) 100000000000000000),
    (exactRationalLiteral (-448736003483437) 100000000000000000),
    (exactRationalLiteral 461957851496033 150000000000000000)
  ],
  ![
    (exactRationalLiteral 109078778897211 20000000000000000),
    (exactRationalLiteral 527999669917523 100000000000000000),
    (exactRationalLiteral 428072992088907 100000000000000000),
    (exactRationalLiteral (-93318174214333) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 533251521350153 100000000000000000),
    (exactRationalLiteral 9544064841053 20000000000000000),
    (exactRationalLiteral (-318287274074853) 100000000000000000),
    (exactRationalLiteral 760074342064223 150000000000000000)
  ],
  ![
    (exactRationalLiteral 21372316007899 50000000000000000),
    (exactRationalLiteral 4072082497533 781250000000000),
    (exactRationalLiteral 4737535596189 500000000000000),
    (exactRationalLiteral (-829467829519103) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-245050972636999) 75000000000000000),
    (exactRationalLiteral (-1200249488857591) 50000000000000000),
    (exactRationalLiteral (-1837774856819771) 50000000000000000),
    (exactRationalLiteral 223886765427899 3750000000000000)
  ],
  ![
    (exactRationalLiteral (-468628511775361) 150000000000000000),
    (exactRationalLiteral 4034841502595879 50000000000000000),
    (exactRationalLiteral 1738884076830581 12500000000000000),
    (exactRationalLiteral (-43377828520127101) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 20675806869279533 300000000000000000),
    (exactRationalLiteral (-1533167833043159) 20000000000000000),
    (exactRationalLiteral (-29149509115515607) 100000000000000000),
    (exactRationalLiteral 61225744742488021 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-4643445232083399) 50000000000000000),
    (exactRationalLiteral (-2123957776730219) 50000000000000000),
    (exactRationalLiteral 15819243150928479 50000000000000000),
    (exactRationalLiteral (-8185421794643431) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 1104327167464579 60000000000000000),
    (exactRationalLiteral 1907134019622529 20000000000000000),
    (exactRationalLiteral (-3412864613166083) 20000000000000000),
    (exactRationalLiteral 208286495496893 3000000000000000)
  ],
  ![
    (exactRationalLiteral 3632883487353533 300000000000000000),
    (exactRationalLiteral (-3632883487353533) 100000000000000000),
    (exactRationalLiteral 3632883487353533 100000000000000000),
    (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
theorem normalizedGeneratorCellMatrix7_eq :
    normalizedGeneratorCellMatrix7 = generatorCellMatrix7 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix7 j a = generatorCellMatrix7 j a := by
    decide +kernel
  exact h k b

end PartialBalayage.Maximal.Square
