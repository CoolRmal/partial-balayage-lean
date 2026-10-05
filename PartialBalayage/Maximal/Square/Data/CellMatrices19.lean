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

/-- Candidate finite rational coefficient matrix on cell (14, 9). -/
def cellMatrix_14_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (14792775957272759 / 180000000000000000 : ℚ),
    (-10981216371625979 / 300000000000000000 : ℚ),
    (-789068522432347 / 150000000000000000 : ℚ),
    (2035322731691977 / 1800000000000000000 : ℚ)
  ],
  ![
    (-131201431401257 / 12500000000000000 : ℚ),
    (-110669520415457 / 25000000000000000 : ℚ),
    (-593915378429283 / 100000000000000000 : ℚ),
    (5171643249383677 / 600000000000000000 : ℚ)
  ],
  ![
    (-52354311937703 / 4687500000000000 : ℚ),
    (-136274702817671 / 10000000000000000 : ℚ),
    (-1498006104561893 / 100000000000000000 : ℚ),
    (8276089180475431 / 600000000000000000 : ℚ)
  ],
  ![
    (-2292386928341257 / 1800000000000000000 : ℚ),
    (1921247210680517 / 200000000000000000 : ℚ),
    (10985324580345773 / 600000000000000000 : ℚ),
    (-12231226480337999 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_9_correct (a b : Fin 4) :
    correctionCellCoefficient 14 9 a b = cellMatrix_14_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 9 a.val b.val = cellMatrix_14_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 10). -/
def cellMatrix_14_10 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (24868987268491843 / 600000000000000000 : ℚ),
    (-26239658191018757 / 600000000000000000 : ℚ),
    (-373650452679137 / 200000000000000000 : ℚ),
    (15860242046508089 / 1800000000000000000 : ℚ)
  ],
  ![
    (-293823448736933 / 24000000000000000 : ℚ),
    (1910625572342889 / 200000000000000000 : ℚ),
    (3983812492525111 / 200000000000000000 : ℚ),
    (-1598003487780341 / 120000000000000000 : ℚ)
  ],
  ![
    (-5196593847994057 / 200000000000000000 : ℚ),
    (-441429294125561 / 200000000000000000 : ℚ),
    (1056015394270329 / 40000000000000000 : ℚ),
    (-6640414896022093 / 600000000000000000 : ℚ)
  ],
  ![
    (23492358748144717 / 1800000000000000000 : ℚ),
    (1090645944019033 / 200000000000000000 : ℚ),
    (-539085135213209 / 24000000000000000 : ℚ),
    (8760368870262097 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_10_correct (a b : Fin 4) :
    correctionCellCoefficient 14 10 a b = cellMatrix_14_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 10 a.val b.val = cellMatrix_14_10 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 11). -/
def cellMatrix_14_11 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (4192687602407557 / 900000000000000000 : ℚ),
    (-420710628686183 / 20000000000000000 : ℚ),
    (7369645344235339 / 300000000000000000 : ℚ),
    (-219420508366851 / 25000000000000000 : ℚ)
  ],
  ![
    (78257017909299 / 20000000000000000 : ℚ),
    (944116559245703 / 100000000000000000 : ℚ),
    (-2003102473188297 / 100000000000000000 : ℚ),
    (1266297715079797 / 150000000000000000 : ℚ)
  ],
  ![
    (-1928563352081503 / 150000000000000000 : ℚ),
    (869577438138909 / 50000000000000000 : ℚ),
    (-85021120291903 / 12500000000000000 : ℚ),
    (50225335121309 / 100000000000000000 : ℚ)
  ],
  ![
    (3465841614616511 / 600000000000000000 : ℚ),
    (-6161581188079157 / 600000000000000000 : ℚ),
    (1347869786731323 / 200000000000000000 : ℚ),
    (-23876987570011 / 14400000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_11_correct (a b : Fin 4) :
    correctionCellCoefficient 14 11 a b = cellMatrix_14_11 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 11 a.val b.val = cellMatrix_14_11 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 12). -/
def cellMatrix_14_12 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-529492956971297 / 900000000000000000 : ℚ),
    (529492956971297 / 300000000000000000 : ℚ),
    (-529492956971297 / 300000000000000000 : ℚ),
    (529492956971297 / 900000000000000000 : ℚ)
  ],
  ![
    (529492956971297 / 300000000000000000 : ℚ),
    (-529492956971297 / 100000000000000000 : ℚ),
    (529492956971297 / 100000000000000000 : ℚ),
    (-529492956971297 / 300000000000000000 : ℚ)
  ],
  ![
    (-529492956971297 / 300000000000000000 : ℚ),
    (529492956971297 / 100000000000000000 : ℚ),
    (-529492956971297 / 100000000000000000 : ℚ),
    (529492956971297 / 300000000000000000 : ℚ)
  ],
  ![
    (529492956971297 / 900000000000000000 : ℚ),
    (-529492956971297 / 300000000000000000 : ℚ),
    (529492956971297 / 300000000000000000 : ℚ),
    (-529492956971297 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_12_correct (a b : Fin 4) :
    correctionCellCoefficient 14 12 a b = cellMatrix_14_12 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 12 a.val b.val = cellMatrix_14_12 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 13). -/
def cellMatrix_14_13 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_14_13_correct (a b : Fin 4) :
    correctionCellCoefficient 14 13 a b = cellMatrix_14_13 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 13 a.val b.val = cellMatrix_14_13 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 0). -/
def cellMatrix_15_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (26790150993114589 / 225000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (15606533007251 / 150000000000000000 : ℚ),
    (1534815446288009 / 1800000000000000000 : ℚ)
  ],
  ![
    (158736349937789 / 50000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (1512285883467 / 10000000000000000 : ℚ),
    (-140903799861089 / 600000000000000000 : ℚ)
  ],
  ![
    (-181831980069869 / 75000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-13252614438931 / 50000000000000000 : ℚ),
    (72867568438241 / 600000000000000000 : ℚ)
  ],
  ![
    (39849598631407 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (14274638691137 / 100000000000000000 : ℚ),
    (-73088517790967 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_0_correct (a b : Fin 4) :
    correctionCellCoefficient 15 0 a b = cellMatrix_15_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 0 a.val b.val = cellMatrix_15_0 a b) a b

end PartialBalayage.Maximal.Square
