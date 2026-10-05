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

/-- Candidate finite rational coefficient matrix on cell (16, 6). -/
def cellMatrix_16_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (54429866964442199 / 450000000000000000 : ℚ),
    (-4616445674317591 / 300000000000000000 : ℚ),
    (-1591962249196889 / 300000000000000000 : ℚ),
    (-544936894530629 / 900000000000000000 : ℚ)
  ],
  ![
    (-2939356136953073 / 150000000000000000 : ℚ),
    (-586715984761903 / 100000000000000000 : ℚ),
    (43851280159547 / 100000000000000000 : ℚ),
    (-63730214294191 / 18750000000000000 : ℚ)
  ],
  ![
    (-586771858388707 / 150000000000000000 : ℚ),
    (18204536881661 / 100000000000000000 : ℚ),
    (205684379451307 / 100000000000000000 : ℚ),
    (-1472670259390709 / 300000000000000000 : ℚ)
  ],
  ![
    (-1016206233652319 / 1800000000000000000 : ℚ),
    (-2032922391501959 / 600000000000000000 : ℚ),
    (-2898571892716451 / 600000000000000000 : ℚ),
    (6920517142425991 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_6_correct (a b : Fin 4) :
    correctionCellCoefficient 16 6 a b = cellMatrix_16_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 6 a.val b.val = cellMatrix_16_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 7). -/
def cellMatrix_16_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (89689573263810329 / 900000000000000000 : ℚ),
    (-4172653533620999 / 150000000000000000 : ℚ),
    (-1068449571863759 / 150000000000000000 : ℚ),
    (-1805506749411679 / 1800000000000000000 : ℚ)
  ],
  ![
    (-852698981642027 / 30000000000000000 : ℚ),
    (-303739370629973 / 20000000000000000 : ℚ),
    (-975832148547509 / 100000000000000000 : ℚ),
    (5892668179407151 / 600000000000000000 : ℚ)
  ],
  ![
    (-1974547227169219 / 300000000000000000 : ℚ),
    (-521548481803217 / 50000000000000000 : ℚ),
    (-633492939969701 / 50000000000000000 : ℚ),
    (10955097906420617 / 600000000000000000 : ℚ)
  ],
  ![
    (-218850533495063 / 200000000000000000 : ℚ),
    (6010968107917121 / 600000000000000000 : ℚ),
    (3647487464045177 / 200000000000000000 : ℚ),
    (-14654490018481601 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_7_correct (a b : Fin 4) :
    correctionCellCoefficient 16 7 a b = cellMatrix_16_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 7 a.val b.val = cellMatrix_16_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 8). -/
def cellMatrix_16_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (38226800837463961 / 600000000000000000 : ℚ),
    (-27043717458805747 / 600000000000000000 : ℚ),
    (-405287002457781 / 40000000000000000 : ℚ),
    (2384463700957843 / 225000000000000000 : ℚ)
  ],
  ![
    (-8709495154539211 / 200000000000000000 : ℚ),
    (-209610824216523 / 40000000000000000 : ℚ),
    (3941003882312133 / 200000000000000000 : ℚ),
    (-60745736196223 / 20000000000000000 : ℚ)
  ],
  ![
    (-2284831203064279 / 200000000000000000 : ℚ),
    (3800960459450141 / 200000000000000000 : ℚ),
    (8421126146541813 / 200000000000000000 : ℚ),
    (-2262159515822249 / 75000000000000000 : ℚ)
  ],
  ![
    (19581656661739187 / 1800000000000000000 : ℚ),
    (-1413087144775019 / 600000000000000000 : ℚ),
    (-18366517644827671 / 600000000000000000 : ℚ),
    (15910713358334609 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_8_correct (a b : Fin 4) :
    correctionCellCoefficient 16 8 a b = cellMatrix_16_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 8 a.val b.val = cellMatrix_16_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 9). -/
def cellMatrix_16_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (34387044633037241 / 1800000000000000000 : ℚ),
    (-20126617924876433 / 600000000000000000 : ℚ),
    (12996404570796029 / 600000000000000000 : ℚ),
    (-9431297893755827 / 1800000000000000000 : ℚ)
  ],
  ![
    (-6424002755271923 / 200000000000000000 : ℚ),
    (5011581557654961 / 200000000000000000 : ℚ),
    (2118631796425443 / 200000000000000000 : ℚ),
    (-378915898231043 / 40000000000000000 : ℚ)
  ],
  ![
    (11714490082205033 / 600000000000000000 : ℚ),
    (101837465038231 / 8000000000000000 : ℚ),
    (-9676149980036179 / 200000000000000000 : ℚ),
    (13241256657076381 / 600000000000000000 : ℚ)
  ],
  ![
    (-176349577564437 / 40000000000000000 : ℚ),
    (-2108231905920381 / 200000000000000000 : ℚ),
    (4484969690613849 / 200000000000000000 : ℚ),
    (-1891112860986861 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_9_correct (a b : Fin 4) :
    correctionCellCoefficient 16 9 a b = cellMatrix_16_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 9 a.val b.val = cellMatrix_16_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 10). -/
def cellMatrix_16_10 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (198061482057789 / 100000000000000000 : ℚ),
    (-594184446173367 / 100000000000000000 : ℚ),
    (594184446173367 / 100000000000000000 : ℚ),
    (-198061482057789 / 100000000000000000 : ℚ)
  ],
  ![
    (-594184446173367 / 100000000000000000 : ℚ),
    (1782553338520101 / 100000000000000000 : ℚ),
    (-1782553338520101 / 100000000000000000 : ℚ),
    (594184446173367 / 100000000000000000 : ℚ)
  ],
  ![
    (594184446173367 / 100000000000000000 : ℚ),
    (-1782553338520101 / 100000000000000000 : ℚ),
    (1782553338520101 / 100000000000000000 : ℚ),
    (-594184446173367 / 100000000000000000 : ℚ)
  ],
  ![
    (-198061482057789 / 100000000000000000 : ℚ),
    (594184446173367 / 100000000000000000 : ℚ),
    (-594184446173367 / 100000000000000000 : ℚ),
    (198061482057789 / 100000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_10_correct (a b : Fin 4) :
    correctionCellCoefficient 16 10 a b = cellMatrix_16_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 10 a.val b.val = cellMatrix_16_10 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 11). -/
def cellMatrix_16_11 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_16_11_correct (a b : Fin 4) :
    correctionCellCoefficient 16 11 a b = cellMatrix_16_11 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 11 a.val b.val = cellMatrix_16_11 a b) a b

end PartialBalayage.Maximal.Square
