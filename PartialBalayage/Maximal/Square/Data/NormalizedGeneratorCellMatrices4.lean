/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.ExactRationalLiteral
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix16
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix17
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix18
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix19

/-!
# Normalized exact generator-cell coefficient cache

Each directly reduced rational is checked by Lean's ordinary kernel, and the
whole finite table is identified with the already proved actual coefficients.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Directly reduced exact coefficient rows for actual generator cell 16. -/
def normalizedGeneratorCellMatrix16 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 1877181189349 96000000000000),
    (exactRationalLiteral 9248845150505847 100000000000000000),
    (exactRationalLiteral (-16806363334116583) 100000000000000000),
    (exactRationalLiteral 6861707475307317 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-28507007501418571) 300000000000000000),
    (exactRationalLiteral (-772273277515791) 20000000000000000),
    (exactRationalLiteral 31338532783654373 100000000000000000),
    (exactRationalLiteral (-48841442465550967) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 6960405452358141 100000000000000000),
    (exactRationalLiteral (-7715040265293841) 100000000000000000),
    (exactRationalLiteral (-29052374032998609) 100000000000000000),
    (exactRationalLiteral 3056520337681621 15000000000000000)
  ],
  ![
    (exactRationalLiteral (-238544320116807) 100000000000000000),
    (exactRationalLiteral 7932035036821263 100000000000000000),
    (exactRationalLiteral 2780087685040407 20000000000000000),
    (exactRationalLiteral (-898958631704483) 6250000000000000)
  ],
  ![
    (exactRationalLiteral (-156565383062809) 75000000000000000),
    (exactRationalLiteral (-114643774161093) 5000000000000000),
    (exactRationalLiteral (-440379702356879) 12500000000000000),
    (exactRationalLiteral 4329818759692111 75000000000000000)
  ],
  ![
    (exactRationalLiteral 24541642188827 10000000000000000),
    (exactRationalLiteral 82807235125523 25000000000000000),
    (exactRationalLiteral 93716765369463 12500000000000000),
    (exactRationalLiteral (-1404803355598931) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-19201179455953) 75000000000000000),
    (exactRationalLiteral (-28733731215813) 25000000000000000),
    (exactRationalLiteral (-98211019129901) 50000000000000000),
    (exactRationalLiteral 6162053573743 2000000000000000)
  ],
  ![
    (exactRationalLiteral (-3251474784967) 2343750000000000),
    (exactRationalLiteral 4709578820791 12500000000000000),
    (exactRationalLiteral 29615452579133 50000000000000000),
    (exactRationalLiteral (-87459647780269) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 247967310461621 300000000000000000),
    (exactRationalLiteral (-7096744093449) 100000000000000000),
    (exactRationalLiteral (-91687538647081) 100000000000000000),
    (exactRationalLiteral 30779466508887 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-178280421589533) 25000000000000000),
    (exactRationalLiteral 14798042226257 10000000000000000),
    (exactRationalLiteral 6507555800511 5000000000000000),
    (exactRationalLiteral (-272700433106579) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1184529716437531 150000000000000000),
    (exactRationalLiteral (-141345698566541) 50000000000000000),
    (exactRationalLiteral (-73309467143693) 50000000000000000),
    (exactRationalLiteral 10817590280863 10000000000000000)
  ],
  ![
    (exactRationalLiteral (-178280421589533) 25000000000000000),
    (exactRationalLiteral 14798042226257 10000000000000000),
    (exactRationalLiteral 6507555800511 5000000000000000),
    (exactRationalLiteral (-272700433106579) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 247967310461621 300000000000000000),
    (exactRationalLiteral (-7096744093449) 100000000000000000),
    (exactRationalLiteral (-91687538647081) 100000000000000000),
    (exactRationalLiteral 30779466508887 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-3251474784967) 2343750000000000),
    (exactRationalLiteral 4709578820791 12500000000000000),
    (exactRationalLiteral 29615452579133 50000000000000000),
    (exactRationalLiteral (-87459647780269) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-19201179455953) 75000000000000000),
    (exactRationalLiteral (-28733731215813) 25000000000000000),
    (exactRationalLiteral (-98211019129901) 50000000000000000),
    (exactRationalLiteral 6162053573743 2000000000000000)
  ],
  ![
    (exactRationalLiteral 24541642188827 10000000000000000),
    (exactRationalLiteral 82807235125523 25000000000000000),
    (exactRationalLiteral 93716765369463 12500000000000000),
    (exactRationalLiteral (-1404803355598931) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-156565383062809) 75000000000000000),
    (exactRationalLiteral (-114643774161093) 5000000000000000),
    (exactRationalLiteral (-440379702356879) 12500000000000000),
    (exactRationalLiteral 4329818759692111 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-238544320116807) 100000000000000000),
    (exactRationalLiteral 7932035036821263 100000000000000000),
    (exactRationalLiteral 2780087685040407 20000000000000000),
    (exactRationalLiteral (-898958631704483) 6250000000000000)
  ],
  ![
    (exactRationalLiteral 6960405452358141 100000000000000000),
    (exactRationalLiteral (-7715040265293841) 100000000000000000),
    (exactRationalLiteral (-29052374032998609) 100000000000000000),
    (exactRationalLiteral 3056520337681621 15000000000000000)
  ],
  ![
    (exactRationalLiteral (-28507007501418571) 300000000000000000),
    (exactRationalLiteral (-772273277515791) 20000000000000000),
    (exactRationalLiteral 31338532783654373 100000000000000000),
    (exactRationalLiteral (-48841442465550967) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1877181189349 96000000000000),
    (exactRationalLiteral 9248845150505847 100000000000000000),
    (exactRationalLiteral (-16806363334116583) 100000000000000000),
    (exactRationalLiteral 6861707475307317 100000000000000000)
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
theorem normalizedGeneratorCellMatrix16_eq :
    normalizedGeneratorCellMatrix16 = generatorCellMatrix16 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix16 j a = generatorCellMatrix16 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 17. -/
def normalizedGeneratorCellMatrix17 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 1270762305314179 75000000000000000),
    (exactRationalLiteral 1246782089272353 12500000000000000),
    (exactRationalLiteral (-8751454840948297) 50000000000000000),
    (exactRationalLiteral 7089078721918493 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-28290619784170507) 300000000000000000),
    (exactRationalLiteral (-4689381577658639) 100000000000000000),
    (exactRationalLiteral 32078032720633811 100000000000000000),
    (exactRationalLiteral (-4940524177947493) 30000000000000000)
  ],
  ![
    (exactRationalLiteral 7210591034634763 100000000000000000),
    (exactRationalLiteral (-7417102434589851) 100000000000000000),
    (exactRationalLiteral (-29249575896613149) 100000000000000000),
    (exactRationalLiteral 30406961046355429 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-62893816642789) 25000000000000000),
    (exactRationalLiteral 199508107945913 2500000000000000),
    (exactRationalLiteral 3449059354978353 25000000000000000),
    (exactRationalLiteral (-42391915259179153) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-15684774050573) 20000000000000000),
    (exactRationalLiteral (-2383712880383293) 100000000000000000),
    (exactRationalLiteral (-3464675943841089) 100000000000000000),
    (exactRationalLiteral 16818172531558247 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-21641892782881) 75000000000000000),
    (exactRationalLiteral 208264517339297 50000000000000000),
    (exactRationalLiteral 45492874862603 6250000000000000),
    (exactRationalLiteral (-1328686877492209) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-387845108642801) 300000000000000000),
    (exactRationalLiteral (-106240502457947) 100000000000000000),
    (exactRationalLiteral (-203148038182541) 100000000000000000),
    (exactRationalLiteral 169844811452867 60000000000000000)
  ],
  ![
    (exactRationalLiteral 136291261293353 300000000000000000),
    (exactRationalLiteral (-5795022334289) 100000000000000000),
    (exactRationalLiteral 92989260406241 100000000000000000),
    (exactRationalLiteral (-143438614037161) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-315534175472521) 60000000000000000),
    (exactRationalLiteral 135582221176431 100000000000000000),
    (exactRationalLiteral (-142549317096359) 100000000000000000),
    (exactRationalLiteral 219169655944117 300000000000000000)
  ],
  ![
    (exactRationalLiteral 351414036759887 75000000000000000),
    (exactRationalLiteral (-62850389320491) 25000000000000000),
    (exactRationalLiteral 22238596767313 12500000000000000),
    (exactRationalLiteral (-9905876018553) 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-315534175472521) 60000000000000000),
    (exactRationalLiteral 135582221176431 100000000000000000),
    (exactRationalLiteral (-142549317096359) 100000000000000000),
    (exactRationalLiteral 219169655944117 300000000000000000)
  ],
  ![
    (exactRationalLiteral 136291261293353 300000000000000000),
    (exactRationalLiteral (-5795022334289) 100000000000000000),
    (exactRationalLiteral 92989260406241 100000000000000000),
    (exactRationalLiteral (-143438614037161) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-387845108642801) 300000000000000000),
    (exactRationalLiteral (-106240502457947) 100000000000000000),
    (exactRationalLiteral (-203148038182541) 100000000000000000),
    (exactRationalLiteral 169844811452867 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-21641892782881) 75000000000000000),
    (exactRationalLiteral 208264517339297 50000000000000000),
    (exactRationalLiteral 45492874862603 6250000000000000),
    (exactRationalLiteral (-1328686877492209) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-15684774050573) 20000000000000000),
    (exactRationalLiteral (-2383712880383293) 100000000000000000),
    (exactRationalLiteral (-3464675943841089) 100000000000000000),
    (exactRationalLiteral 16818172531558247 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-62893816642789) 25000000000000000),
    (exactRationalLiteral 199508107945913 2500000000000000),
    (exactRationalLiteral 3449059354978353 25000000000000000),
    (exactRationalLiteral (-42391915259179153) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 7210591034634763 100000000000000000),
    (exactRationalLiteral (-7417102434589851) 100000000000000000),
    (exactRationalLiteral (-29249575896613149) 100000000000000000),
    (exactRationalLiteral 30406961046355429 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-28290619784170507) 300000000000000000),
    (exactRationalLiteral (-4689381577658639) 100000000000000000),
    (exactRationalLiteral 32078032720633811 100000000000000000),
    (exactRationalLiteral (-4940524177947493) 30000000000000000)
  ],
  ![
    (exactRationalLiteral 1270762305314179 75000000000000000),
    (exactRationalLiteral 1246782089272353 12500000000000000),
    (exactRationalLiteral (-8751454840948297) 50000000000000000),
    (exactRationalLiteral 7089078721918493 100000000000000000)
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
theorem normalizedGeneratorCellMatrix17_eq :
    normalizedGeneratorCellMatrix17 = generatorCellMatrix17 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix17 j a = generatorCellMatrix17 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 18. -/
def normalizedGeneratorCellMatrix18 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 4470091865280079 300000000000000000),
    (exactRationalLiteral 10061442084134053 100000000000000000),
    (exactRationalLiteral (-17327209058841119) 100000000000000000),
    (exactRationalLiteral 5240023136548663 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-27554339796993853) 300000000000000000),
    (exactRationalLiteral (-5102332135105291) 100000000000000000),
    (exactRationalLiteral 31564346196097709 100000000000000000),
    (exactRationalLiteral (-240866229624541) 1500000000000000)
  ],
  ![
    (exactRationalLiteral 887321766174287 12000000000000000),
    (exactRationalLiteral (-6819116101515809) 100000000000000000),
    (exactRationalLiteral (-28595677839265741) 100000000000000000),
    (exactRationalLiteral 11719512769923583 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-481132775936747) 150000000000000000),
    (exactRationalLiteral 938138470436597 12500000000000000),
    (exactRationalLiteral 6676748293858579 50000000000000000),
    (exactRationalLiteral (-40219529735048423) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-25575324246697) 12000000000000000),
    (exactRationalLiteral (-2113759602194737) 100000000000000000),
    (exactRationalLiteral (-3258174634674979) 100000000000000000),
    (exactRationalLiteral 15595962396765647 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-46678667329993) 30000000000000000),
    (exactRationalLiteral 168343739220653 50000000000000000),
    (exactRationalLiteral 323038009540897 50000000000000000),
    (exactRationalLiteral (-1817866628455997) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 36998915811629 100000000000000000),
    (exactRationalLiteral (-106693729596129) 100000000000000000),
    (exactRationalLiteral (-193887967668081) 100000000000000000),
    (exactRationalLiteral 869960039735243 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-43106328411821) 9375000000000000),
    (exactRationalLiteral 6965324292783 10000000000000000),
    (exactRationalLiteral 38310169423879 50000000000000000),
    (exactRationalLiteral (-182060924201993) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 118429596645487 37500000000000000),
    (exactRationalLiteral (-33331258362557) 25000000000000000),
    (exactRationalLiteral (-3739515644173) 6250000000000000),
    (exactRationalLiteral 44459472272677 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-43106328411821) 9375000000000000),
    (exactRationalLiteral 6965324292783 10000000000000000),
    (exactRationalLiteral 38310169423879 50000000000000000),
    (exactRationalLiteral (-182060924201993) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 36998915811629 100000000000000000),
    (exactRationalLiteral (-106693729596129) 100000000000000000),
    (exactRationalLiteral (-193887967668081) 100000000000000000),
    (exactRationalLiteral 869960039735243 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-46678667329993) 30000000000000000),
    (exactRationalLiteral 168343739220653 50000000000000000),
    (exactRationalLiteral 323038009540897 50000000000000000),
    (exactRationalLiteral (-1817866628455997) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-25575324246697) 12000000000000000),
    (exactRationalLiteral (-2113759602194737) 100000000000000000),
    (exactRationalLiteral (-3258174634674979) 100000000000000000),
    (exactRationalLiteral 15595962396765647 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-481132775936747) 150000000000000000),
    (exactRationalLiteral 938138470436597 12500000000000000),
    (exactRationalLiteral 6676748293858579 50000000000000000),
    (exactRationalLiteral (-40219529735048423) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 887321766174287 12000000000000000),
    (exactRationalLiteral (-6819116101515809) 100000000000000000),
    (exactRationalLiteral (-28595677839265741) 100000000000000000),
    (exactRationalLiteral 11719512769923583 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-27554339796993853) 300000000000000000),
    (exactRationalLiteral (-5102332135105291) 100000000000000000),
    (exactRationalLiteral 31564346196097709 100000000000000000),
    (exactRationalLiteral (-240866229624541) 1500000000000000)
  ],
  ![
    (exactRationalLiteral 4470091865280079 300000000000000000),
    (exactRationalLiteral 10061442084134053 100000000000000000),
    (exactRationalLiteral (-17327209058841119) 100000000000000000),
    (exactRationalLiteral 5240023136548663 75000000000000000)
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
theorem normalizedGeneratorCellMatrix18_eq :
    normalizedGeneratorCellMatrix18 = generatorCellMatrix18 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix18 j a = generatorCellMatrix18 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 19. -/
def normalizedGeneratorCellMatrix19 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 3632883487353533 300000000000000000),
    (exactRationalLiteral (-3632883487353533) 100000000000000000),
    (exactRationalLiteral 3632883487353533 100000000000000000),
    (exactRationalLiteral (-3632883487353533) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1219485487025067 100000000000000000),
    (exactRationalLiteral 9853114332181927 100000000000000000),
    (exactRationalLiteral (-16608899728810491) 100000000000000000),
    (exactRationalLiteral 19986792427124773 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-636594345459239) 7500000000000000),
    (exactRationalLiteral (-84576686412959) 1562500000000000),
    (exactRationalLiteral 15000943005176087 50000000000000000),
    (exactRationalLiteral (-45346587452154683) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1426267851113859 20000000000000000),
    (exactRationalLiteral (-6007428796121331) 100000000000000000),
    (exactRationalLiteral (-5373206629466253) 20000000000000000),
    (exactRationalLiteral 4536128553468597 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-579611710005463) 150000000000000000),
    (exactRationalLiteral 870731690652619 12500000000000000),
    (exactRationalLiteral 3084446940522667 25000000000000000),
    (exactRationalLiteral (-18487257987234629) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-9017417481583) 2343750000000000),
    (exactRationalLiteral (-20068937403071) 1000000000000000),
    (exactRationalLiteral (-14948286189151) 500000000000000),
    (exactRationalLiteral 4815093195663449 100000000000000000)
  ],
  ![
    (exactRationalLiteral 31684678151 120000000000000),
    (exactRationalLiteral 46936296850369 12500000000000000),
    (exactRationalLiteral 338036036033581 50000000000000000),
    (exactRationalLiteral (-1857954877740083) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-652351806127747) 150000000000000000),
    (exactRationalLiteral (-882674548629) 625000000000000),
    (exactRationalLiteral (-71875377389057) 25000000000000000),
    (exactRationalLiteral 25805725604529 6250000000000000)
  ],
  ![
    (exactRationalLiteral 63472175552897 30000000000000000),
    (exactRationalLiteral 6883649786149 50000000000000000),
    (exactRationalLiteral 103462291664647 50000000000000000),
    (exactRationalLiteral (-108598203824509) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-652351806127747) 150000000000000000),
    (exactRationalLiteral (-882674548629) 625000000000000),
    (exactRationalLiteral (-71875377389057) 25000000000000000),
    (exactRationalLiteral 25805725604529 6250000000000000)
  ],
  ![
    (exactRationalLiteral 31684678151 120000000000000),
    (exactRationalLiteral 46936296850369 12500000000000000),
    (exactRationalLiteral 338036036033581 50000000000000000),
    (exactRationalLiteral (-1857954877740083) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-9017417481583) 2343750000000000),
    (exactRationalLiteral (-20068937403071) 1000000000000000),
    (exactRationalLiteral (-14948286189151) 500000000000000),
    (exactRationalLiteral 4815093195663449 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-579611710005463) 150000000000000000),
    (exactRationalLiteral 870731690652619 12500000000000000),
    (exactRationalLiteral 3084446940522667 25000000000000000),
    (exactRationalLiteral (-18487257987234629) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 1426267851113859 20000000000000000),
    (exactRationalLiteral (-6007428796121331) 100000000000000000),
    (exactRationalLiteral (-5373206629466253) 20000000000000000),
    (exactRationalLiteral 4536128553468597 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-636594345459239) 7500000000000000),
    (exactRationalLiteral (-84576686412959) 1562500000000000),
    (exactRationalLiteral 15000943005176087 50000000000000000),
    (exactRationalLiteral (-45346587452154683) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1219485487025067 100000000000000000),
    (exactRationalLiteral 9853114332181927 100000000000000000),
    (exactRationalLiteral (-16608899728810491) 100000000000000000),
    (exactRationalLiteral 19986792427124773 300000000000000000)
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
theorem normalizedGeneratorCellMatrix19_eq :
    normalizedGeneratorCellMatrix19 = generatorCellMatrix19 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix19 j a = generatorCellMatrix19 j a := by
    decide +kernel
  exact h k b

end PartialBalayage.Maximal.Square
