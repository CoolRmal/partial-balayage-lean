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

/-- Candidate finite rational coefficient matrix on cell (7, 2). -/
def cellMatrix_7_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-58832201362583071 / 200000000000000000 : ℚ),
    (5949084622787381 / 600000000000000000 : ℚ),
    (4756397721142893 / 200000000000000000 : ℚ),
    (369993694479881 / 600000000000000000 : ℚ)
  ],
  ![
    (38645566284421421 / 200000000000000000 : ℚ),
    (1624938658128051 / 200000000000000000 : ℚ),
    (-1911924828795543 / 200000000000000000 : ℚ),
    (-146585173561651 / 120000000000000000 : ℚ)
  ],
  ![
    (-9244477186313103 / 200000000000000000 : ℚ),
    (-183180852063581 / 40000000000000000 : ℚ),
    (391850143786269 / 200000000000000000 : ℚ),
    (4572609585237 / 8000000000000000 : ℚ)
  ],
  ![
    (638860291511187 / 100000000000000000 : ℚ),
    (28316275974463 / 30000000000000000 : ℚ),
    (-22049965886111 / 100000000000000000 : ℚ),
    (-200796664768711 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_2_correct (a b : Fin 4) :
    correctionCellCoefficient 7 2 a b = cellMatrix_7_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 2 a.val b.val = cellMatrix_7_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (7, 3). -/
def cellMatrix_7_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-19488541575881659 / 75000000000000000 : ℚ),
    (17798726016542191 / 300000000000000000 : ℚ),
    (2563195707811387 / 100000000000000000 : ℚ),
    (-2996186222833417 / 900000000000000000 : ℚ)
  ],
  ![
    (28585703618363383 / 150000000000000000 : ℚ),
    (-293183686727129 / 20000000000000000 : ℚ),
    (-1322425348301899 / 100000000000000000 : ℚ),
    (1557399994427 / 300000000000000000 : ℚ)
  ],
  ![
    (-4827108031606907 / 100000000000000000 : ℚ),
    (13171359134213 / 12500000000000000 : ℚ),
    (183698965669761 / 50000000000000000 : ℚ),
    (49918120002869 / 75000000000000000 : ℚ)
  ],
  ![
    (12600765754950437 / 1800000000000000000 : ℚ),
    (100929264087217 / 600000000000000000 : ℚ),
    (-333096460085377 / 600000000000000000 : ℚ),
    (-214213371805261 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_3_correct (a b : Fin 4) :
    correctionCellCoefficient 7 3 a b = cellMatrix_7_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 3 a.val b.val = cellMatrix_7_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (7, 4). -/
def cellMatrix_7_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-160393745713484269 / 900000000000000000 : ℚ),
    (1257571418357379 / 12500000000000000 : ℚ),
    (586675112575093 / 37500000000000000 : ℚ),
    (-388004595009843 / 40000000000000000 : ℚ)
  ],
  ![
    (48807933290908561 / 300000000000000000 : ℚ),
    (-513651466280627 / 12500000000000000 : ℚ),
    (-82554246769217 / 6250000000000000 : ℚ),
    (3833562231621373 / 600000000000000000 : ℚ)
  ],
  ![
    (-12863345201569567 / 300000000000000000 : ℚ),
    (4061871936579 / 390625000000000 : ℚ),
    (283535205675499 / 50000000000000000 : ℚ),
    (-535814352187611 / 200000000000000000 : ℚ)
  ],
  ![
    (765055828223029 / 120000000000000000 : ℚ),
    (-331230133231353 / 200000000000000000 : ℚ),
    (-253841067898633 / 200000000000000000 : ℚ),
    (1026164464995881 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_4_correct (a b : Fin 4) :
    correctionCellCoefficient 7 4 a b = cellMatrix_7_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 4 a.val b.val = cellMatrix_7_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (7, 5). -/
def cellMatrix_7_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-128997008555344433 / 1800000000000000000 : ℚ),
    (61676824908114233 / 600000000000000000 : ℚ),
    (-8073404974241447 / 600000000000000000 : ℚ),
    (-1978619514277211 / 1800000000000000000 : ℚ)
  ],
  ![
    (22956316914041189 / 200000000000000000 : ℚ),
    (-9668333022098547 / 200000000000000000 : ℚ),
    (1191826335006429 / 200000000000000000 : ℚ),
    (89443161531811 / 200000000000000000 : ℚ)
  ],
  ![
    (-3538535139402127 / 120000000000000000 : ℚ),
    (2740517020369607 / 200000000000000000 : ℚ),
    (-473302233860837 / 200000000000000000 : ℚ),
    (-35960822152643 / 600000000000000000 : ℚ)
  ],
  ![
    (3618180539085721 / 900000000000000000 : ℚ),
    (-186321542761247 / 75000000000000000 : ℚ),
    (132320630649991 / 300000000000000000 : ℚ),
    (-45959915702017 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_5_correct (a b : Fin 4) :
    correctionCellCoefficient 7 5 a b = cellMatrix_7_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 5 a.val b.val = cellMatrix_7_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (7, 6). -/
def cellMatrix_7_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (14917315865998357 / 900000000000000000 : ℚ),
    (2721962215334633 / 37500000000000000 : ℚ),
    (-5026012244259329 / 300000000000000000 : ℚ),
    (2853185949275921 / 1800000000000000000 : ℚ)
  ],
  ![
    (7284626694240441 / 100000000000000000 : ℚ),
    (-438521929218141 / 12500000000000000 : ℚ),
    (730077909800931 / 100000000000000000 : ℚ),
    (-738642604184731 / 600000000000000000 : ℚ)
  ],
  ![
    (-1365874019954621 / 75000000000000000 : ℚ),
    (175795173049529 / 20000000000000000 : ℚ),
    (-12731576400337 / 5000000000000000 : ℚ),
    (-17912403051199 / 600000000000000000 : ℚ)
  ],
  ![
    (3512607920099443 / 1800000000000000000 : ℚ),
    (-1007249735192029 / 600000000000000000 : ℚ),
    (43736269119593 / 120000000000000000 : ℚ),
    (313404130689341 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_6_correct (a b : Fin 4) :
    correctionCellCoefficient 7 6 a b = cellMatrix_7_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 6 a.val b.val = cellMatrix_7_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (7, 7). -/
def cellMatrix_7_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (26637186110355809 / 360000000000000000 : ℚ),
    (26300532417592733 / 600000000000000000 : ℚ),
    (-7198838539242737 / 600000000000000000 : ℚ),
    (7605765010451 / 9375000000000000 : ℚ)
  ],
  ![
    (26300532417592733 / 600000000000000000 : ℚ),
    (-4834681832471263 / 200000000000000000 : ℚ),
    (721513215417131 / 200000000000000000 : ℚ),
    (-42747152217793 / 100000000000000000 : ℚ)
  ],
  ![
    (-7198838539242737 / 600000000000000000 : ℚ),
    (721513215417131 / 200000000000000000 : ℚ),
    (-527175459064679 / 200000000000000000 : ℚ),
    (88680912714551 / 100000000000000000 : ℚ)
  ],
  ![
    (7605765010451 / 9375000000000000 : ℚ),
    (-42747152217793 / 100000000000000000 : ℚ),
    (88680912714551 / 100000000000000000 : ℚ),
    (-132222068294741 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_7_correct (a b : Fin 4) :
    correctionCellCoefficient 7 7 a b = cellMatrix_7_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 7 a.val b.val = cellMatrix_7_7 a b) a b

end PartialBalayage.Maximal.Square
