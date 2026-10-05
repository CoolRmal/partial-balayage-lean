/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CellMatrix

/-!
# Rational cell matrices checked against the actual signed spline correction

The literals are candidate data derived from the immutable supplementary coefficient file.
Each matrix is identified with the actual signed coefficients by ordinary rational proofs.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Candidate finite rational coefficient matrix on cell (4, 2). -/
def cellMatrix_4_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-1101061040010621613 / 600000000000000000 : ℚ),
    (-34166512346293669 / 120000000000000000 : ℚ),
    (-7377280807705339 / 200000000000000000 : ℚ),
    (103815951346108903 / 900000000000000000 : ℚ)
  ],
  ![
    (704462305345405879 / 600000000000000000 : ℚ),
    (88707987224621289 / 200000000000000000 : ℚ),
    (10873098238833773 / 40000000000000000 : ℚ),
    (-126634005791675731 / 300000000000000000 : ℚ)
  ],
  ![
    (-80705964746125663 / 200000000000000000 : ℚ),
    (-60702494405706323 / 200000000000000000 : ℚ),
    (-55423309610813403 / 200000000000000000 : ℚ),
    (140762961137334871 / 300000000000000000 : ℚ)
  ],
  ![
    (134489892106776233 / 1800000000000000000 : ℚ),
    (50925756162379597 / 600000000000000000 : ℚ),
    (54397328152406351 / 600000000000000000 : ℚ),
    (-296802388014804373 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_4_2_correct (a b : Fin 4) :
    correctionCellCoefficient 4 2 a b = cellMatrix_4_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 4 2 a.val b.val = cellMatrix_4_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (4, 3). -/
def cellMatrix_4_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-3674444429803400119 / 1800000000000000000 : ℚ),
    (-2488114628494191 / 200000000000000000 : ℚ),
    (185500060269101789 / 600000000000000000 : ℚ),
    (6317892889106299 / 225000000000000000 : ℚ)
  ],
  ![
    (880414729018424879 / 600000000000000000 : ℚ),
    (-55829041970392443 / 200000000000000000 : ℚ),
    (-198902520389182597 / 200000000000000000 : ℚ),
    (148929438912935819 / 300000000000000000 : ℚ)
  ],
  ![
    (-12358775360530657 / 24000000000000000 : ℚ),
    (109976808647336613 / 200000000000000000 : ℚ),
    (226102612663856339 / 200000000000000000 : ℚ),
    (-1852902706153441 / 2400000000000000 : ℚ)
  ],
  ![
    (19207094629541213 / 225000000000000000 : ℚ),
    (-68540987773806037 / 300000000000000000 : ℚ),
    (-121202529931199011 / 300000000000000000 : ℚ),
    (542097167488049173 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_4_3_correct (a b : Fin 4) :
    correctionCellCoefficient 4 3 a b = cellMatrix_4_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 4 3 a.val b.val = cellMatrix_4_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (4, 4). -/
def cellMatrix_4_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-3089794137539692079 / 1800000000000000000 : ℚ),
    (138026306588523799 / 200000000000000000 : ℚ),
    (236043203381952181 / 600000000000000000 : ℚ),
    (-442707181705651411 / 1800000000000000000 : ℚ)
  ],
  ![
    (138026306588523799 / 200000000000000000 : ℚ),
    (-155775204922885999 / 200000000000000000 : ℚ),
    (98956357436689041 / 200000000000000000 : ℚ),
    (-15958985556871789 / 120000000000000000 : ℚ)
  ],
  ![
    (236043203381952181 / 600000000000000000 : ℚ),
    (98956357436689041 / 200000000000000000 : ℚ),
    (-237123063874503911 / 200000000000000000 : ℚ),
    (299692107625651151 / 600000000000000000 : ℚ)
  ],
  ![
    (-442707181705651411 / 1800000000000000000 : ℚ),
    (-15958985556871789 / 120000000000000000 : ℚ),
    (299692107625651151 / 600000000000000000 : ℚ),
    (-891597116686589 / 4000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_4_4_correct (a b : Fin 4) :
    correctionCellCoefficient 4 4 a b = cellMatrix_4_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 4 4 a.val b.val = cellMatrix_4_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (5, 0). -/
def cellMatrix_5_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-691962468714808687 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-57970003719659893 / 300000000000000000 : ℚ),
    (7856601797951633 / 100000000000000000 : ℚ)
  ],
  ![
    (39968292075734617 / 100000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (14013198261038133 / 100000000000000000 : ℚ),
    (-2656943129816207 / 50000000000000000 : ℚ)
  ],
  ![
    (-28733404922016883 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-5720735118600229 / 100000000000000000 : ℚ),
    (85245513088939 / 4000000000000000 : ℚ)
  ],
  ![
    (3941132597262341 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (48888610002163 / 4000000000000000 : ℚ),
    (-1660770760339987 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_5_0_correct (a b : Fin 4) :
    correctionCellCoefficient 5 0 a b = cellMatrix_5_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 5 0 a.val b.val = cellMatrix_5_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (5, 1). -/
def cellMatrix_5_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-795163063692223669 / 900000000000000000 : ℚ),
    (-45230591257755089 / 300000000000000000 : ℚ),
    (3184853115476201 / 75000000000000000 : ℚ),
    (451650694443389 / 225000000000000000 : ℚ)
  ],
  ![
    (3041725254821271 / 6250000000000000 : ℚ),
    (755296108948689 / 6250000000000000 : ℚ),
    (-1928460517859109 / 100000000000000000 : ℚ),
    (147760096722219 / 50000000000000000 : ℚ)
  ],
  ![
    (-7900439359229429 / 60000000000000000 : ℚ),
    (-5048056755530033 / 100000000000000000 : ℚ),
    (168169590767549 / 25000000000000000 : ℚ),
    (-592834546136861 / 150000000000000000 : ℚ)
  ],
  ![
    (37342816282847461 / 1800000000000000000 : ℚ),
    (1272545839789793 / 120000000000000000 : ℚ),
    (-194112460275097 / 120000000000000000 : ℚ),
    (299943367527619 / 225000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_5_1_correct (a b : Fin 4) :
    correctionCellCoefficient 5 1 a b = cellMatrix_5_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 5 1 a.val b.val = cellMatrix_5_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (5, 2). -/
def cellMatrix_5_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-111353749662750121 / 112500000000000000 : ℚ),
    (-717806542246877 / 12000000000000000 : ℚ),
    (363650380991959 / 7500000000000000 : ℚ),
    (-4396753248631727 / 1800000000000000000 : ℚ)
  ],
  ![
    (59119401495904689 / 100000000000000000 : ℚ),
    (227859432194853 / 2500000000000000 : ℚ),
    (-208379987505159 / 20000000000000000 : ℚ),
    (12981444951183649 / 600000000000000000 : ℚ)
  ],
  ![
    (-26907000532900189 / 150000000000000000 : ℚ),
    (-4888369121663363 / 100000000000000000 : ℚ),
    (-256495364601763 / 50000000000000000 : ℚ),
    (-15276465740134631 / 600000000000000000 : ℚ)
  ],
  ![
    (6213207101754317 / 200000000000000000 : ℚ),
    (6821151536418947 / 600000000000000000 : ℚ),
    (476328212948489 / 200000000000000000 : ℚ),
    (5295346780419869 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_5_2_correct (a b : Fin 4) :
    correctionCellCoefficient 5 2 a b = cellMatrix_5_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 5 2 a.val b.val = cellMatrix_5_2 a b) a b

end PartialBalayage.Maximal.Square
