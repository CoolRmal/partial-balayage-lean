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

/-- Candidate finite rational coefficient matrix on cell (9, 9). -/
def cellMatrix_9_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (77568773965256347 / 900000000000000000 : ℚ),
    (-4786268622394339 / 100000000000000000 : ℚ),
    (-1244701510315261 / 60000000000000000 : ℚ),
    (346123588807991 / 18000000000000000 : ℚ)
  ],
  ![
    (-4786268622394339 / 100000000000000000 : ℚ),
    (-6005760043122717 / 100000000000000000 : ℚ),
    (-3279732741970149 / 100000000000000000 : ℚ),
    (3220703253351523 / 100000000000000000 : ℚ)
  ],
  ![
    (-1244701510315261 / 60000000000000000 : ℚ),
    (-3279732741970149 / 100000000000000000 : ℚ),
    (-2879246474787893 / 100000000000000000 : ℚ),
    (7723875993678331 / 300000000000000000 : ℚ)
  ],
  ![
    (346123588807991 / 18000000000000000 : ℚ),
    (3220703253351523 / 100000000000000000 : ℚ),
    (7723875993678331 / 300000000000000000 : ℚ),
    (-16376501113392703 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_9_correct (a b : Fin 4) :
    correctionCellCoefficient 9 9 a b = cellMatrix_9_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 9 a.val b.val = cellMatrix_9_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 0). -/
def cellMatrix_10_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (2724594853272103 / 180000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-2908642340420527 / 300000000000000000 : ℚ),
    (84721999762841 / 14400000000000000 : ℚ)
  ],
  ![
    (13702442702949569 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (540608485032959 / 100000000000000000 : ℚ),
    (-1490017164047723 / 600000000000000000 : ℚ)
  ],
  ![
    (-502497940559579 / 60000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-154586450589349 / 100000000000000000 : ℚ),
    (406191769945483 / 600000000000000000 : ℚ)
  ],
  ![
    (216836527794631 / 180000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (94601750519129 / 300000000000000000 : ℚ),
    (-680519415137 / 4687500000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_0_correct (a b : Fin 4) :
    correctionCellCoefficient 10 0 a b = cellMatrix_10_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 0 a.val b.val = cellMatrix_10_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 1). -/
def cellMatrix_10_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (20384344460552993 / 1800000000000000000 : ℚ),
    (-348106463775661 / 200000000000000000 : ℚ),
    (4772965289514071 / 600000000000000000 : ℚ),
    (-31307231740133 / 200000000000000000 : ℚ)
  ],
  ![
    (29158519152049169 / 600000000000000000 : ℚ),
    (672416776084113 / 200000000000000000 : ℚ),
    (-81760038796361 / 40000000000000000 : ℚ),
    (-47064363035707 / 200000000000000000 : ℚ)
  ],
  ![
    (-5546306339186401 / 600000000000000000 : ℚ),
    (-212154032411913 / 200000000000000000 : ℚ),
    (19403773753357 / 40000000000000000 : ℚ),
    (-3503465041473 / 200000000000000000 : ℚ)
  ],
  ![
    (618664081412119 / 450000000000000000 : ℚ),
    (29271886665977 / 150000000000000000 : ℚ),
    (-1442319087487 / 12000000000000000 : ℚ),
    (9367411157451 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_1_correct (a b : Fin 4) :
    correctionCellCoefficient 10 1 a b = cellMatrix_10_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 1 a.val b.val = cellMatrix_10_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 2). -/
def cellMatrix_10_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (1564425853472653 / 90000000000000000 : ℚ),
    (4109923051019981 / 300000000000000000 : ℚ),
    (2245600101926437 / 300000000000000000 : ℚ),
    (-60055669956499 / 112500000000000000 : ℚ)
  ],
  ![
    (7452043952312243 / 150000000000000000 : ℚ),
    (-143188350493309 / 100000000000000000 : ℚ),
    (-274996641544463 / 100000000000000000 : ℚ),
    (-3888601811299 / 75000000000000000 : ℚ)
  ],
  ![
    (-1475555556311551 / 150000000000000000 : ℚ),
    (-14313345001381 / 100000000000000000 : ℚ),
    (43254236821183 / 100000000000000000 : ℚ),
    (7380653581559 / 60000000000000000 : ℚ)
  ],
  ![
    (2693877802934209 / 1800000000000000000 : ℚ),
    (57162338332267 / 600000000000000000 : ℚ),
    (12190746042709 / 600000000000000000 : ℚ),
    (-109934270197787 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_2_correct (a b : Fin 4) :
    correctionCellCoefficient 10 2 a b = cellMatrix_10_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 2 a.val b.val = cellMatrix_10_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 3). -/
def cellMatrix_10_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (534849728654903 / 14062500000000000 : ℚ),
    (8120677895220863 / 300000000000000000 : ℚ),
    (353030948454889 / 60000000000000000 : ℚ),
    (-3259694521088423 / 1800000000000000000 : ℚ)
  ],
  ![
    (2272329753544329 / 50000000000000000 : ℚ),
    (-708736040827431 / 100000000000000000 : ℚ),
    (-290551048789659 / 100000000000000000 : ℚ),
    (244086369066287 / 600000000000000000 : ℚ)
  ],
  ![
    (-2827385169255901 / 300000000000000000 : ℚ),
    (5454919827439 / 5000000000000000 : ℚ),
    (40078752364489 / 50000000000000000 : ℚ),
    (-79747959428543 / 600000000000000000 : ℚ)
  ],
  ![
    (55840055717227 / 36000000000000000 : ℚ),
    (-14195219890051 / 300000000000000000 : ℚ),
    (-48871762077539 / 300000000000000000 : ℚ),
    (2103590147981 / 36000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_3_correct (a b : Fin 4) :
    correctionCellCoefficient 10 3 a b = cellMatrix_10_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 3 a.val b.val = cellMatrix_10_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 4). -/
def cellMatrix_10_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (124516066571711009 / 1800000000000000000 : ℚ),
    (20042280238451083 / 600000000000000000 : ℚ),
    (270614963460467 / 600000000000000000 : ℚ),
    (-1474381461573817 / 600000000000000000 : ℚ)
  ],
  ![
    (4303264174779139 / 120000000000000000 : ℚ),
    (-2335589907747211 / 200000000000000000 : ℚ),
    (-337015728513031 / 200000000000000000 : ℚ),
    (152946911971881 / 200000000000000000 : ℚ)
  ],
  ![
    (-4598982890273797 / 600000000000000000 : ℚ),
    (459078852584929 / 200000000000000000 : ℚ),
    (80567050029413 / 200000000000000000 : ℚ),
    (-30675604243699 / 200000000000000000 : ℚ)
  ],
  ![
    (13993224452527 / 10000000000000000 : ℚ),
    (-4945749195467 / 25000000000000000 : ℚ),
    (619665270331 / 50000000000000000 : ℚ),
    (829176399349 / 37500000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_4_correct (a b : Fin 4) :
    correctionCellCoefficient 10 4 a b = cellMatrix_10_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 4 a.val b.val = cellMatrix_10_4 a b) a b

end PartialBalayage.Maximal.Square
