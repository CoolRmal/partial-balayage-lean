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

/-- Candidate finite rational coefficient matrix on cell (13, 5). -/
def cellMatrix_13_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (259492035122581373 / 1800000000000000000 : ℚ),
    (807061187678963 / 120000000000000000 : ℚ),
    (-2860915543538059 / 600000000000000000 : ℚ),
    (-44492080193143 / 200000000000000000 : ℚ)
  ],
  ![
    (3572525497958113 / 600000000000000000 : ℚ),
    (-728769450868121 / 200000000000000000 : ℚ),
    (118894102311409 / 200000000000000000 : ℚ),
    (57413140850011 / 600000000000000000 : ℚ)
  ],
  ![
    (-2221402659444139 / 600000000000000000 : ℚ),
    (29980986668887 / 200000000000000000 : ℚ),
    (-23310106807603 / 200000000000000000 : ℚ),
    (-19689649498073 / 200000000000000000 : ℚ)
  ],
  ![
    (76749967059283 / 900000000000000000 : ℚ),
    (-2513399944863 / 20000000000000000 : ℚ),
    (-12632385242213 / 300000000000000000 : ℚ),
    (4423363722143 / 75000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_5_correct (a b : Fin 4) :
    correctionCellCoefficient 13 5 a b = cellMatrix_13_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 5 a.val b.val = cellMatrix_13_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 6). -/
def cellMatrix_13_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (131307388792706677 / 900000000000000000 : ℚ),
    (-208695387041959 / 60000000000000000 : ℚ),
    (-1630672132638173 / 300000000000000000 : ℚ),
    (-18791938575957 / 200000000000000000 : ℚ)
  ],
  ![
    (450078148284497 / 150000000000000000 : ℚ),
    (-108392026348823 / 50000000000000000 : ℚ),
    (8815362158071 / 10000000000000000 : ℚ),
    (113058751754701 / 600000000000000000 : ℚ)
  ],
  ![
    (-1130229484177253 / 300000000000000000 : ℚ),
    (-37854087720269 / 100000000000000000 : ℚ),
    (-41189527650911 / 100000000000000000 : ℚ),
    (3376376993939 / 40000000000000000 : ℚ)
  ],
  ![
    (-846792860819 / 36000000000000000 : ℚ),
    (-1977080998331 / 60000000000000000 : ℚ),
    (40447979423503 / 300000000000000000 : ℚ),
    (-321463586954381 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_6_correct (a b : Fin 4) :
    correctionCellCoefficient 13 6 a b = cellMatrix_13_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 6 a.val b.val = cellMatrix_13_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 7). -/
def cellMatrix_13_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (246400755731141933 / 1800000000000000000 : ℚ),
    (-585251323210393 / 40000000000000000 : ℚ),
    (-3430471712459959 / 600000000000000000 : ℚ),
    (-60006303940391 / 180000000000000000 : ℚ)
  ],
  ![
    (380529586063691 / 200000000000000000 : ℚ),
    (32105132682249 / 200000000000000000 : ℚ),
    (289365994916121 / 200000000000000000 : ℚ),
    (19126521590913 / 100000000000000000 : ℚ)
  ],
  ![
    (-2684075005672501 / 600000000000000000 : ℚ),
    (-189820631135097 / 200000000000000000 : ℚ),
    (-31733400392737 / 200000000000000000 : ℚ),
    (-203186025860929 / 300000000000000000 : ℚ)
  ],
  ![
    (-60142594468081 / 600000000000000000 : ℚ),
    (-59814159747893 / 200000000000000000 : ℚ),
    (-641513674953 / 1600000000000000 : ℚ),
    (1134714226046597 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_7_correct (a b : Fin 4) :
    correctionCellCoefficient 13 7 a b = cellMatrix_13_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 7 a.val b.val = cellMatrix_13_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 8). -/
def cellMatrix_13_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (23241440889987829 / 200000000000000000 : ℚ),
    (-16239776312479723 / 600000000000000000 : ℚ),
    (-1343511583954623 / 200000000000000000 : ℚ),
    (-1276779090452531 / 1800000000000000000 : ℚ)
  ],
  ![
    (740253756843887 / 200000000000000000 : ℚ),
    (725596252059969 / 200000000000000000 : ℚ),
    (404125124461599 / 200000000000000000 : ℚ),
    (375521310906253 / 200000000000000000 : ℚ)
  ],
  ![
    (-1251703050659287 / 200000000000000000 : ℚ),
    (-659659483642429 / 200000000000000000 : ℚ),
    (-87621090422919 / 40000000000000000 : ℚ),
    (715597847199457 / 600000000000000000 : ℚ)
  ],
  ![
    (-38217984926351 / 225000000000000000 : ℚ),
    (59267061323521 / 75000000000000000 : ℚ),
    (447073298969611 / 300000000000000000 : ℚ),
    (-416765120214787 / 180000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_8_correct (a b : Fin 4) :
    correctionCellCoefficient 13 8 a b = cellMatrix_13_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 8 a.val b.val = cellMatrix_13_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 9). -/
def cellMatrix_13_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (73542627863203577 / 900000000000000000 : ℚ),
    (-1065734371110833 / 25000000000000000 : ℚ),
    (-13268284605791 / 1500000000000000 : ℚ),
    (71107179896989 / 72000000000000000 : ℚ)
  ],
  ![
    (561374111067927 / 50000000000000000 : ℚ),
    (1330205216850963 / 100000000000000000 : ℚ),
    (765344528590179 / 100000000000000000 : ℚ),
    (-1809554084024671 / 600000000000000000 : ℚ)
  ],
  ![
    (-1583201528012369 / 150000000000000000 : ℚ),
    (-410136270336081 / 100000000000000000 : ℚ),
    (138746197542431 / 100000000000000000 : ℚ),
    (-1294891847067083 / 600000000000000000 : ℚ)
  ],
  ![
    (-92136453994127 / 450000000000000000 : ℚ),
    (-952610757840629 / 300000000000000000 : ℚ),
    (-409188075526081 / 75000000000000000 : ℚ),
    (1595163504590419 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_9_correct (a b : Fin 4) :
    correctionCellCoefficient 13 9 a b = cellMatrix_13_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 9 a.val b.val = cellMatrix_13_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 10). -/
def cellMatrix_13_10 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (56208118976902703 / 1800000000000000000 : ℚ),
    (-11471524364622689 / 200000000000000000 : ℚ),
    (-141185373795667 / 24000000000000000 : ℚ),
    (5930392469238929 / 600000000000000000 : ℚ)
  ],
  ![
    (3500046744287461 / 120000000000000000 : ℚ),
    (3912234464037971 / 200000000000000000 : ℚ),
    (-278865026844313 / 200000000000000000 : ℚ),
    (2469561540190873 / 200000000000000000 : ℚ)
  ],
  ![
    (-9256038395878459 / 600000000000000000 : ℚ),
    (-1560179597569521 / 200000000000000000 : ℚ),
    (-1017399451982221 / 200000000000000000 : ℚ),
    (-2919429054484077 / 200000000000000000 : ℚ)
  ],
  ![
    (-197929473378241 / 56250000000000000 : ℚ),
    (27968757586099 / 15000000000000000 : ℚ),
    (3148738211666933 / 300000000000000000 : ℚ),
    (1058936133715069 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_10_correct (a b : Fin 4) :
    correctionCellCoefficient 13 10 a b = cellMatrix_13_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 10 a.val b.val = cellMatrix_13_10 a b) a b

end PartialBalayage.Maximal.Square
