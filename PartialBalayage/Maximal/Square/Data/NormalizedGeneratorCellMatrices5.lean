/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.ExactRationalLiteral
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix20
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix21
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix22
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix23

/-!
# Normalized exact generator-cell coefficient cache

Each directly reduced rational is checked by Lean's ordinary kernel, and the
whole finite table is identified with the already proved actual coefficients.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Directly reduced exact coefficient rows for actual generator cell 20. -/
def normalizedGeneratorCellMatrix20 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 2956572969244151 300000000000000000),
    (exactRationalLiteral 9244276638120289 100000000000000000),
    (exactRationalLiteral (-15344701441802509) 100000000000000000),
    (exactRationalLiteral 18394913843643619 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-7597608474008913) 100000000000000000),
    (exactRationalLiteral (-5305952449160697) 100000000000000000),
    (exactRationalLiteral 27567509494291899 100000000000000000),
    (exactRationalLiteral (-1294864918334479) 9375000000000000)
  ],
  ![
    (exactRationalLiteral 1648098705621223 25000000000000000),
    (exactRationalLiteral (-533308692506697) 10000000000000000),
    (exactRationalLiteral (-2463672821237859) 10000000000000000),
    (exactRationalLiteral 2069072717873129 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-1698602785064177) 300000000000000000),
    (exactRationalLiteral 6459071371022847 100000000000000000),
    (exactRationalLiteral 11455622349160147 100000000000000000),
    (exactRationalLiteral (-4262474121601681) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-120502679873081) 75000000000000000),
    (exactRationalLiteral (-198827523654289) 10000000000000000),
    (exactRationalLiteral (-759959420853251) 25000000000000000),
    (exactRationalLiteral 93533314626223 2000000000000000)
  ],
  ![
    (exactRationalLiteral (-676108547624353) 150000000000000000),
    (exactRationalLiteral 65305485265537 12500000000000000),
    (exactRationalLiteral 237793329865291 25000000000000000),
    (exactRationalLiteral (-151799905662719) 10000000000000000)
  ],
  ![
    (exactRationalLiteral 71335295606279 50000000000000000),
    (exactRationalLiteral (-220584582182593) 50000000000000000),
    (exactRationalLiteral (-330930523633389) 50000000000000000),
    (exactRationalLiteral 1384703961180463 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-676108547624353) 150000000000000000),
    (exactRationalLiteral 65305485265537 12500000000000000),
    (exactRationalLiteral 237793329865291 25000000000000000),
    (exactRationalLiteral (-151799905662719) 10000000000000000)
  ],
  ![
    (exactRationalLiteral (-120502679873081) 75000000000000000),
    (exactRationalLiteral (-198827523654289) 10000000000000000),
    (exactRationalLiteral (-759959420853251) 25000000000000000),
    (exactRationalLiteral 93533314626223 2000000000000000)
  ],
  ![
    (exactRationalLiteral (-1698602785064177) 300000000000000000),
    (exactRationalLiteral 6459071371022847 100000000000000000),
    (exactRationalLiteral 11455622349160147 100000000000000000),
    (exactRationalLiteral (-4262474121601681) 37500000000000000)
  ],
  ![
    (exactRationalLiteral 1648098705621223 25000000000000000),
    (exactRationalLiteral (-533308692506697) 10000000000000000),
    (exactRationalLiteral (-2463672821237859) 10000000000000000),
    (exactRationalLiteral 2069072717873129 12500000000000000)
  ],
  ![
    (exactRationalLiteral (-7597608474008913) 100000000000000000),
    (exactRationalLiteral (-5305952449160697) 100000000000000000),
    (exactRationalLiteral 27567509494291899 100000000000000000),
    (exactRationalLiteral (-1294864918334479) 9375000000000000)
  ],
  ![
    (exactRationalLiteral 2956572969244151 300000000000000000),
    (exactRationalLiteral 9244276638120289 100000000000000000),
    (exactRationalLiteral (-15344701441802509) 100000000000000000),
    (exactRationalLiteral 18394913843643619 300000000000000000)
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
theorem normalizedGeneratorCellMatrix20_eq :
    normalizedGeneratorCellMatrix20 = generatorCellMatrix20 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix20 j a = generatorCellMatrix20 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 21. -/
def normalizedGeneratorCellMatrix21 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 2556168326663539 300000000000000000),
    (exactRationalLiteral 8393389152719773 100000000000000000),
    (exactRationalLiteral (-13868167892411429) 100000000000000000),
    (exactRationalLiteral 16605557262257257 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-1706209642993909) 25000000000000000),
    (exactRationalLiteral (-2474399060434527) 50000000000000000),
    (exactRationalLiteral 12510508508288253 50000000000000000),
    (exactRationalLiteral (-37510647123533389) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 17945685402671357 300000000000000000),
    (exactRationalLiteral (-4729476903470307) 100000000000000000),
    (exactRationalLiteral (-22644170623653301) 100000000000000000),
    (exactRationalLiteral 7573617258907291 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-384088071356639) 75000000000000000),
    (exactRationalLiteral 745255823820569 12500000000000000),
    (exactRationalLiteral 5495079755260223 50000000000000000),
    (exactRationalLiteral (-32424273441443831) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-185670332546737) 37500000000000000),
    (exactRationalLiteral (-1064603324417473) 50000000000000000),
    (exactRationalLiteral (-1801411925210203) 50000000000000000),
    (exactRationalLiteral 15560830671164369 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-27917734724323) 75000000000000000),
    (exactRationalLiteral 125564582932773 12500000000000000),
    (exactRationalLiteral 526886718773537 25000000000000000),
    (exactRationalLiteral (-770493086674507) 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-185670332546737) 37500000000000000),
    (exactRationalLiteral (-1064603324417473) 50000000000000000),
    (exactRationalLiteral (-1801411925210203) 50000000000000000),
    (exactRationalLiteral 15560830671164369 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-384088071356639) 75000000000000000),
    (exactRationalLiteral 745255823820569 12500000000000000),
    (exactRationalLiteral 5495079755260223 50000000000000000),
    (exactRationalLiteral (-32424273441443831) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 17945685402671357 300000000000000000),
    (exactRationalLiteral (-4729476903470307) 100000000000000000),
    (exactRationalLiteral (-22644170623653301) 100000000000000000),
    (exactRationalLiteral 7573617258907291 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-1706209642993909) 25000000000000000),
    (exactRationalLiteral (-2474399060434527) 50000000000000000),
    (exactRationalLiteral 12510508508288253 50000000000000000),
    (exactRationalLiteral (-37510647123533389) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 2556168326663539 300000000000000000),
    (exactRationalLiteral 8393389152719773 100000000000000000),
    (exactRationalLiteral (-13868167892411429) 100000000000000000),
    (exactRationalLiteral 16605557262257257 300000000000000000)
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
theorem normalizedGeneratorCellMatrix21_eq :
    normalizedGeneratorCellMatrix21 = generatorCellMatrix21 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix21 j a = generatorCellMatrix21 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 22. -/
def normalizedGeneratorCellMatrix22 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 2231493847662059 300000000000000000),
    (exactRationalLiteral 7582588788750569 100000000000000000),
    (exactRationalLiteral (-12489630106956883) 100000000000000000),
    (exactRationalLiteral 373578769151501 7500000000000000)
  ],
  ![
    (exactRationalLiteral (-18733553625255721) 300000000000000000),
    (exactRationalLiteral (-4576114597333163) 100000000000000000),
    (exactRationalLiteral 4559506585958089 20000000000000000),
    (exactRationalLiteral (-5682850583845561) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 16895992576384607 300000000000000000),
    (exactRationalLiteral (-4481907829838387) 100000000000000000),
    (exactRationalLiteral (-4286822786184677) 20000000000000000),
    (exactRationalLiteral 1340794067610161 9375000000000000)
  ],
  ![
    (exactRationalLiteral (-1040207828991861) 100000000000000000),
    (exactRationalLiteral 6225976321488611 100000000000000000),
    (exactRationalLiteral 11958006820743963 100000000000000000),
    (exactRationalLiteral (-17701693568627627) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-1069868166119) 15000000000000000),
    (exactRationalLiteral (-1006576656610901) 25000000000000000),
    (exactRationalLiteral (-27884258457031) 390625000000000),
    (exactRationalLiteral 599554961691219 6250000000000000)
  ],
  ![
    (exactRationalLiteral (-1040207828991861) 100000000000000000),
    (exactRationalLiteral 6225976321488611 100000000000000000),
    (exactRationalLiteral 11958006820743963 100000000000000000),
    (exactRationalLiteral (-17701693568627627) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 16895992576384607 300000000000000000),
    (exactRationalLiteral (-4481907829838387) 100000000000000000),
    (exactRationalLiteral (-4286822786184677) 20000000000000000),
    (exactRationalLiteral 1340794067610161 9375000000000000)
  ],
  ![
    (exactRationalLiteral (-18733553625255721) 300000000000000000),
    (exactRationalLiteral (-4576114597333163) 100000000000000000),
    (exactRationalLiteral 4559506585958089 20000000000000000),
    (exactRationalLiteral (-5682850583845561) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 2231493847662059 300000000000000000),
    (exactRationalLiteral 7582588788750569 100000000000000000),
    (exactRationalLiteral (-12489630106956883) 100000000000000000),
    (exactRationalLiteral 373578769151501 7500000000000000)
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
theorem normalizedGeneratorCellMatrix22_eq :
    normalizedGeneratorCellMatrix22 = generatorCellMatrix22 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix22 j a = generatorCellMatrix22 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 23. -/
def normalizedGeneratorCellMatrix23 : Fin 53 → Fin 4 → ℚ := ![
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
    (exactRationalLiteral 2453520659103157 300000000000000000),
    (exactRationalLiteral (-2453520659103157) 100000000000000000),
    (exactRationalLiteral 2453520659103157 100000000000000000),
    (exactRationalLiteral (-2453520659103157) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1833597869042759 300000000000000000),
    (exactRationalLiteral 6921847759174361 100000000000000000),
    (exactRationalLiteral (-11299570573282921) 100000000000000000),
    (exactRationalLiteral 13488431980337201 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-5982220847458519) 100000000000000000),
    (exactRationalLiteral (-888945105632001) 20000000000000000),
    (exactRationalLiteral 21471296232601767 100000000000000000),
    (exactRationalLiteral (-1277128285648559) 12000000000000000)
  ],
  ![
    (exactRationalLiteral 3205587760493377 60000000000000000),
    (exactRationalLiteral (-5261397174278717) 100000000000000000),
    (exactRationalLiteral (-23445380316511291) 100000000000000000),
    (exactRationalLiteral 15191090429157201 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-592098697059311) 37500000000000000),
    (exactRationalLiteral 2618897801183759 25000000000000000),
    (exactRationalLiteral 1352516749761161 6250000000000000),
    (exactRationalLiteral (-3084996933436459) 18750000000000000)
  ],
  ![
    (exactRationalLiteral 3205587760493377 60000000000000000),
    (exactRationalLiteral (-5261397174278717) 100000000000000000),
    (exactRationalLiteral (-23445380316511291) 100000000000000000),
    (exactRationalLiteral 15191090429157201 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-5982220847458519) 100000000000000000),
    (exactRationalLiteral (-888945105632001) 20000000000000000),
    (exactRationalLiteral 21471296232601767 100000000000000000),
    (exactRationalLiteral (-1277128285648559) 12000000000000000)
  ],
  ![
    (exactRationalLiteral 1833597869042759 300000000000000000),
    (exactRationalLiteral 6921847759174361 100000000000000000),
    (exactRationalLiteral (-11299570573282921) 100000000000000000),
    (exactRationalLiteral 13488431980337201 300000000000000000)
  ],
  ![
    (exactRationalLiteral 2453520659103157 300000000000000000),
    (exactRationalLiteral (-2453520659103157) 100000000000000000),
    (exactRationalLiteral 2453520659103157 100000000000000000),
    (exactRationalLiteral (-2453520659103157) 300000000000000000)
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
theorem normalizedGeneratorCellMatrix23_eq :
    normalizedGeneratorCellMatrix23 = generatorCellMatrix23 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix23 j a = generatorCellMatrix23 j a := by
    decide +kernel
  exact h k b

end PartialBalayage.Maximal.Square
