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

/-- Candidate finite rational coefficient matrix on cell (12, 12). -/
def cellMatrix_12_12 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-8967022579286669 / 56250000000000000 : ℚ),
    (2304266242293871 / 30000000000000000 : ℚ),
    (8895927032242849 / 75000000000000000 : ℚ),
    (-446995836444133 / 6250000000000000 : ℚ)
  ],
  ![
    (2304266242293871 / 30000000000000000 : ℚ),
    (-3105985205593813 / 25000000000000000 : ℚ),
    (4351529446503707 / 50000000000000000 : ℚ),
    (-307171286887283 / 12500000000000000 : ℚ)
  ],
  ![
    (8895927032242849 / 75000000000000000 : ℚ),
    (4351529446503707 / 50000000000000000 : ℚ),
    (-3243492127491071 / 10000000000000000 : ℚ),
    (2988689694855577 / 20000000000000000 : ℚ)
  ],
  ![
    (-446995836444133 / 6250000000000000 : ℚ),
    (-307171286887283 / 12500000000000000 : ℚ),
    (2988689694855577 / 20000000000000000 : ℚ),
    (-128177911297148767 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_12_correct (a b : Fin 4) :
    correctionCellCoefficient 12 12 a b = cellMatrix_12_12 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 12 a.val b.val = cellMatrix_12_12 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 0). -/
def cellMatrix_13_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (2276908865749763 / 22500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-372862552697017 / 300000000000000000 : ℚ),
    (637271536211543 / 360000000000000000 : ℚ)
  ],
  ![
    (2345279520491599 / 150000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (121777652557601 / 100000000000000000 : ℚ),
    (-135948763346983 / 200000000000000000 : ℚ)
  ],
  ![
    (-143708619995057 / 37500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-29818186610509 / 100000000000000000 : ℚ),
    (14044317181289 / 120000000000000000 : ℚ)
  ],
  ![
    (2434410326691 / 10000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (1550832497743 / 100000000000000000 : ℚ),
    (-4147458994429 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_0_correct (a b : Fin 4) :
    correctionCellCoefficient 13 0 a b = cellMatrix_13_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 0 a.val b.val = cellMatrix_13_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 1). -/
def cellMatrix_13_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (183101891624856653 / 1800000000000000000 : ℚ),
    (564969156756549 / 200000000000000000 : ℚ),
    (2440632575663681 / 600000000000000000 : ℚ),
    (-164367718838371 / 360000000000000000 : ℚ)
  ],
  ![
    (9703937707271053 / 600000000000000000 : ℚ),
    (15852864037891 / 40000000000000000 : ℚ),
    (-164290984925747 / 200000000000000000 : ℚ),
    (-17642746428233 / 600000000000000000 : ℚ)
  ],
  ![
    (-2408025453677521 / 600000000000000000 : ℚ),
    (-49051160535591 / 200000000000000000 : ℚ),
    (10585212685427 / 200000000000000000 : ℚ),
    (15106295368489 / 600000000000000000 : ℚ)
  ],
  ![
    (28613370360931 / 112500000000000000 : ℚ),
    (5157535992029 / 300000000000000000 : ℚ),
    (1262596247 / 750000000000000 : ℚ),
    (-4147099678501 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_1_correct (a b : Fin 4) :
    correctionCellCoefficient 13 1 a b = cellMatrix_13_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 1 a.val b.val = cellMatrix_13_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 2). -/
def cellMatrix_13_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (32447778861410797 / 300000000000000000 : ℚ),
    (2877167013702577 / 300000000000000000 : ℚ),
    (269798996911971 / 100000000000000000 : ℚ),
    (-892520818127497 / 1800000000000000000 : ℚ)
  ],
  ![
    (1178901870829243 / 75000000000000000 : ℚ),
    (-8342512377821 / 6250000000000000 : ℚ),
    (-9096686567699 / 10000000000000000 : ℚ),
    (28073418331127 / 600000000000000000 : ℚ)
  ],
  ![
    (-209026416821627 / 50000000000000000 : ℚ),
    (-1596804974531 / 25000000000000000 : ℚ),
    (6422877013479 / 50000000000000000 : ℚ),
    (-1853626034069 / 120000000000000000 : ℚ)
  ],
  ![
    (26400054111437 / 100000000000000000 : ℚ),
    (-2126586367373 / 300000000000000000 : ℚ),
    (-1298193476367 / 50000000000000000 : ℚ),
    (8475998245073 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_2_correct (a b : Fin 4) :
    correctionCellCoefficient 13 2 a b = cellMatrix_13_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 2 a.val b.val = cellMatrix_13_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 3). -/
def cellMatrix_13_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (8636541455078729 / 72000000000000000 : ℚ),
    (8099401172221309 / 600000000000000000 : ℚ),
    (726273163344329 / 600000000000000000 : ℚ),
    (-1690999590160711 / 1800000000000000000 : ℚ)
  ],
  ![
    (1622521200526463 / 120000000000000000 : ℚ),
    (-120550888093421 / 40000000000000000 : ℚ),
    (-153860313022853 / 200000000000000000 : ℚ),
    (108335913178067 / 600000000000000000 : ℚ)
  ],
  ![
    (-495766785451373 / 120000000000000000 : ℚ),
    (29340446141239 / 200000000000000000 : ℚ),
    (16423377883571 / 200000000000000000 : ℚ),
    (-12659743157731 / 600000000000000000 : ℚ)
  ],
  ![
    (424182488897489 / 1800000000000000000 : ℚ),
    (-26933817922481 / 600000000000000000 : ℚ),
    (-7102323471331 / 600000000000000000 : ℚ),
    (-63214650833 / 120000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_3_correct (a b : Fin 4) :
    correctionCellCoefficient 13 3 a b = cellMatrix_13_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 3 a.val b.val = cellMatrix_13_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 4). -/
def cellMatrix_13_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (60174889948376107 / 450000000000000000 : ℚ),
    (982618488593657 / 75000000000000000 : ℚ),
    (-482363213408191 / 300000000000000000 : ℚ),
    (-1896189116721677 / 1800000000000000000 : ℚ)
  ],
  ![
    (495924804611709 / 50000000000000000 : ℚ),
    (-100267394166843 / 25000000000000000 : ℚ),
    (-22762199922393 / 100000000000000000 : ℚ),
    (32883700431239 / 120000000000000000 : ℚ)
  ],
  ![
    (-1177101099170083 / 300000000000000000 : ℚ),
    (990549175013 / 4000000000000000 : ℚ),
    (47045434073 / 2500000000000000 : ℚ),
    (-27073741533443 / 600000000000000000 : ℚ)
  ],
  ![
    (160562922476779 / 900000000000000000 : ℚ),
    (-21043342313819 / 300000000000000000 : ℚ),
    (-4025271616913 / 300000000000000000 : ℚ),
    (-28690378751 / 3000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_4_correct (a b : Fin 4) :
    correctionCellCoefficient 13 4 a b = cellMatrix_13_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 4 a.val b.val = cellMatrix_13_4 a b) a b

end PartialBalayage.Maximal.Square
