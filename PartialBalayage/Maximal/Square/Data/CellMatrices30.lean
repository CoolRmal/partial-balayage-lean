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

/-- Candidate finite rational coefficient matrix on cell (20, 6). -/
def cellMatrix_20_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (1688946349157141 / 900000000000000000 : ℚ),
    (-1688946349157141 / 300000000000000000 : ℚ),
    (1688946349157141 / 300000000000000000 : ℚ),
    (-1688946349157141 / 900000000000000000 : ℚ)
  ],
  ![
    (-1688946349157141 / 300000000000000000 : ℚ),
    (1688946349157141 / 100000000000000000 : ℚ),
    (-1688946349157141 / 100000000000000000 : ℚ),
    (1688946349157141 / 300000000000000000 : ℚ)
  ],
  ![
    (1688946349157141 / 300000000000000000 : ℚ),
    (-1688946349157141 / 100000000000000000 : ℚ),
    (1688946349157141 / 100000000000000000 : ℚ),
    (-1688946349157141 / 300000000000000000 : ℚ)
  ],
  ![
    (-1688946349157141 / 900000000000000000 : ℚ),
    (1688946349157141 / 300000000000000000 : ℚ),
    (-1688946349157141 / 300000000000000000 : ℚ),
    (1688946349157141 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_6_correct (a b : Fin 4) :
    correctionCellCoefficient 20 6 a b = cellMatrix_20_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 6 a.val b.val = cellMatrix_20_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (20, 7). -/
def cellMatrix_20_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ],
  ![
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ],
  ![
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ],
  ![
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_7_correct (a b : Fin 4) :
    correctionCellCoefficient 20 7 a b = cellMatrix_20_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 7 a.val b.val = cellMatrix_20_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (21, 0). -/
def cellMatrix_21_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (69377619369820159 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-768478921278107 / 300000000000000000 : ℚ),
    (-27917734724323 / 900000000000000000 : ℚ)
  ],
  ![
    (-852402476134441 / 60000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-261532654520387 / 100000000000000000 : ℚ),
    (41854860977591 / 50000000000000000 : ℚ)
  ],
  ![
    (-202086648874223 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-255256842521939 / 100000000000000000 : ℚ),
    (526886718773537 / 300000000000000000 : ℚ)
  ],
  ![
    (-184999459766167 / 450000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (860658927357007 / 300000000000000000 : ℚ),
    (-770493086674507 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_21_0_correct (a b : Fin 4) :
    correctionCellCoefficient 21 0 a b = cellMatrix_21_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 21 0 a.val b.val = cellMatrix_21_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (21, 1). -/
def cellMatrix_21_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (4469617658084101 / 60000000000000000 : ℚ),
    (-1564875577280537 / 300000000000000000 : ℚ),
    (-26546555200081 / 10000000000000000 : ℚ),
    (-770599064911271 / 900000000000000000 : ℚ)
  ],
  ![
    (-239774058918391 / 15000000000000000 : ℚ),
    (-67984035793807 / 25000000000000000 : ℚ),
    (-10403488654841 / 100000000000000000 : ℚ),
    (-813474158551927 / 300000000000000000 : ℚ)
  ],
  ![
    (-146990152555501 / 100000000000000000 : ℚ),
    (16373033729659 / 100000000000000000 : ℚ),
    (135814938125799 / 50000000000000000 : ℚ),
    (-637262603218333 / 150000000000000000 : ℚ)
  ],
  ![
    (-49750698742417 / 450000000000000000 : ℚ),
    (-590161405309507 / 300000000000000000 : ℚ),
    (-725410166333257 / 150000000000000000 : ℚ),
    (10937872151117327 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_21_1_correct (a b : Fin 4) :
    correctionCellCoefficient 21 1 a b = cellMatrix_21_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 21 1 a.val b.val = cellMatrix_21_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (21, 2). -/
def cellMatrix_21_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (59189849106501343 / 900000000000000000 : ℚ),
    (-982066988549167 / 75000000000000000 : ℚ),
    (-1566995720913701 / 300000000000000000 : ℚ),
    (-512925069208183 / 300000000000000000 : ℚ)
  ],
  ![
    (-1075995705401659 / 50000000000000000 : ℚ),
    (-1106217279036837 / 100000000000000000 : ℚ),
    (-51492352950423 / 6250000000000000 : ℚ),
    (2167549136730349 / 300000000000000000 : ℚ)
  ],
  ![
    (-425743467079699 / 150000000000000000 : ℚ),
    (-714892420203811 / 100000000000000000 : ℚ),
    (-250723832546267 / 25000000000000000 : ℚ),
    (1406851516274519 / 100000000000000000 : ℚ)
  ],
  ![
    (-1507021071708467 / 1800000000000000000 : ℚ),
    (3954268009832257 / 600000000000000000 : ℚ),
    (8036231485784299 / 600000000000000000 : ℚ),
    (-895266720430271 / 75000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_21_2_correct (a b : Fin 4) :
    correctionCellCoefficient 21 2 a b = cellMatrix_21_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 21 2 a.val b.val = cellMatrix_21_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (21, 3). -/
def cellMatrix_21_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (41165282873545687 / 900000000000000000 : ℚ),
    (-8601034603648619 / 300000000000000000 : ℚ),
    (-12423083714153 / 1200000000000000 : ℚ),
    (14868134987422259 / 1800000000000000000 : ℚ)
  ],
  ![
    (-503935493720521 / 15000000000000000 : ℚ),
    (-73302929590003 / 12500000000000000 : ℚ),
    (1343671489523581 / 100000000000000000 : ℚ),
    (-394378630009609 / 600000000000000000 : ℚ)
  ],
  ![
    (-892147818251239 / 150000000000000000 : ℚ),
    (149987146824961 / 10000000000000000 : ℚ),
    (3217659218638489 / 100000000000000000 : ℚ),
    (-14203061526006187 / 600000000000000000 : ℚ)
  ],
  ![
    (12978076124814697 / 1800000000000000000 : ℚ),
    (-486556769641883 / 200000000000000000 : ℚ),
    (-2690033960908441 / 120000000000000000 : ℚ),
    (3992550377186207 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_21_3_correct (a b : Fin 4) :
    correctionCellCoefficient 21 3 a b = cellMatrix_21_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 21 3 a.val b.val = cellMatrix_21_3 a b) a b

end PartialBalayage.Maximal.Square
