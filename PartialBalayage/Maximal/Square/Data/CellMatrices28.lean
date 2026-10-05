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

/-- Candidate finite rational coefficient matrix on cell (19, 3). -/
def cellMatrix_19_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (170722675045678523 / 1800000000000000000 : ℚ),
    (-306684922835741 / 40000000000000000 : ℚ),
    (-1964266060635367 / 600000000000000000 : ℚ),
    (-2062360476756133 / 1800000000000000000 : ℚ)
  ],
  ![
    (-2150641924978229 / 120000000000000000 : ℚ),
    (-1047709097943751 / 200000000000000000 : ℚ),
    (-7937593269959 / 40000000000000000 : ℚ),
    (-1765747643498639 / 600000000000000000 : ℚ)
  ],
  ![
    (-1398701861730553 / 600000000000000000 : ℚ),
    (29679211194357 / 200000000000000000 : ℚ),
    (340198020010361 / 200000000000000000 : ℚ),
    (-2497624383654619 / 600000000000000000 : ℚ)
  ],
  ![
    (-40987831643327 / 90000000000000000 : ℚ),
    (-803479586394647 / 300000000000000000 : ℚ),
    (-73888774248611 / 18750000000000000 : ℚ),
    (11533651845229537 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_3_correct (a b : Fin 4) :
    correctionCellCoefficient 19 3 a b = cellMatrix_19_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 3 a.val b.val = cellMatrix_19_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 4). -/
def cellMatrix_19_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (18620836857425993 / 225000000000000000 : ℚ),
    (-1765194406760497 / 100000000000000000 : ℚ),
    (-8053253074783 / 1200000000000000 : ℚ),
    (-357953766307451 / 200000000000000000 : ℚ)
  ],
  ![
    (-2630191410211737 / 100000000000000000 : ℚ),
    (-144641633707099 / 10000000000000000 : ℚ),
    (-902717804924217 / 100000000000000000 : ℚ),
    (1733368627240771 / 200000000000000000 : ℚ)
  ],
  ![
    (-1393347275885509 / 300000000000000000 : ℚ),
    (-89377456621977 / 10000000000000000 : ℚ),
    (-1078713181822129 / 100000000000000000 : ℚ),
    (3280054459478683 / 200000000000000000 : ℚ)
  ],
  ![
    (-400101544623847 / 600000000000000000 : ℚ),
    (5197811120529139 / 600000000000000000 : ℚ),
    (611280737951599 / 40000000000000000 : ℚ),
    (-8480288043079907 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_4_correct (a b : Fin 4) :
    correctionCellCoefficient 19 4 a b = cellMatrix_19_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 4 a.val b.val = cellMatrix_19_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 5). -/
def cellMatrix_19_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (101891732028777439 / 1800000000000000000 : ℚ),
    (-21866003412113041 / 600000000000000000 : ℚ),
    (-7248210434158559 / 600000000000000000 : ℚ),
    (1009579659441157 / 100000000000000000 : ℚ)
  ],
  ![
    (-8225282477173117 / 200000000000000000 : ℚ),
    (-260719602423307 / 40000000000000000 : ℚ),
    (3394670271873879 / 200000000000000000 : ℚ),
    (-134553819066503 / 100000000000000000 : ℚ)
  ],
  ![
    (-4781457661586363 / 600000000000000000 : ℚ),
    (3737761518707993 / 200000000000000000 : ℚ),
    (7682737014791791 / 200000000000000000 : ℚ),
    (-354705620185317 / 12500000000000000 : ℚ)
  ],
  ![
    (548663260209937 / 60000000000000000 : ℚ),
    (-476157717540653 / 150000000000000000 : ℚ),
    (-677985544165239 / 25000000000000000 : ℚ),
    (9664226170794481 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_5_correct (a b : Fin 4) :
    correctionCellCoefficient 19 5 a b = cellMatrix_19_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 5 a.val b.val = cellMatrix_19_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 6). -/
def cellMatrix_19_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (6544304871980693 / 360000000000000000 : ℚ),
    (-18189990410489333 / 600000000000000000 : ℚ),
    (10924223435782267 / 600000000000000000 : ℚ),
    (-3645669974214367 / 900000000000000000 : ℚ)
  ],
  ![
    (-6403317855548779 / 200000000000000000 : ℚ),
    (935683923446441 / 40000000000000000 : ℚ),
    (2587347357474861 / 200000000000000000 : ℚ),
    (-3110115422414197 / 300000000000000000 : ℚ)
  ],
  ![
    (12454168170017773 / 600000000000000000 : ℚ),
    (2077365779396359 / 200000000000000000 : ℚ),
    (-373725310164137 / 8000000000000000 : ℚ),
    (6488008120728479 / 300000000000000000 : ℚ)
  ],
  ![
    (-1008475052411499 / 200000000000000000 : ℚ),
    (-5455258477710641 / 600000000000000000 : ℚ),
    (4240341817472569 / 200000000000000000 : ℚ),
    (-408847723494281 / 45000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_6_correct (a b : Fin 4) :
    correctionCellCoefficient 19 6 a b = cellMatrix_19_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 6 a.val b.val = cellMatrix_19_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 7). -/
def cellMatrix_19_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (3632883487353533 / 1800000000000000000 : ℚ),
    (-3632883487353533 / 600000000000000000 : ℚ),
    (3632883487353533 / 600000000000000000 : ℚ),
    (-3632883487353533 / 1800000000000000000 : ℚ)
  ],
  ![
    (-3632883487353533 / 600000000000000000 : ℚ),
    (3632883487353533 / 200000000000000000 : ℚ),
    (-3632883487353533 / 200000000000000000 : ℚ),
    (3632883487353533 / 600000000000000000 : ℚ)
  ],
  ![
    (3632883487353533 / 600000000000000000 : ℚ),
    (-3632883487353533 / 200000000000000000 : ℚ),
    (3632883487353533 / 200000000000000000 : ℚ),
    (-3632883487353533 / 600000000000000000 : ℚ)
  ],
  ![
    (-3632883487353533 / 1800000000000000000 : ℚ),
    (3632883487353533 / 600000000000000000 : ℚ),
    (-3632883487353533 / 600000000000000000 : ℚ),
    (3632883487353533 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_7_correct (a b : Fin 4) :
    correctionCellCoefficient 19 7 a b = cellMatrix_19_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 7 a.val b.val = cellMatrix_19_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 8). -/
def cellMatrix_19_8 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_19_8_correct (a b : Fin 4) :
    correctionCellCoefficient 19 8 a b = cellMatrix_19_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 8 a.val b.val = cellMatrix_19_8 a b) a b

end PartialBalayage.Maximal.Square
