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

/-- Candidate finite rational coefficient matrix on cell (21, 4). -/
def cellMatrix_21_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (26957867541392419 / 1800000000000000000 : ℚ),
    (-14757017934027979 / 600000000000000000 : ℚ),
    (8656593130345759 / 600000000000000000 : ℚ),
    (-5606380728504649 / 1800000000000000000 : ℚ)
  ],
  ![
    (-16008310062009107 / 600000000000000000 : ℚ),
    (3807460454644667 / 200000000000000000 : ℚ),
    (2292964349037553 / 200000000000000000 : ℚ),
    (-5343176750878663 / 600000000000000000 : ℚ)
  ],
  ![
    (10533531322317451 / 600000000000000000 : ℚ),
    (1667318285046989 / 200000000000000000 : ℚ),
    (-7767743088729209 / 200000000000000000 : ℚ),
    (10817955490570319 / 600000000000000000 : ℚ)
  ],
  ![
    (-7796141952471623 / 1800000000000000000 : ℚ),
    (-4404707654892817 / 600000000000000000 : ℚ),
    (10505132458575037 / 600000000000000000 : ℚ),
    (-13555344860416147 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_21_4_correct (a b : Fin 4) :
    correctionCellCoefficient 21 4 a b = cellMatrix_21_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 21 4 a.val b.val = cellMatrix_21_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (21, 5). -/
def cellMatrix_21_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (101673746728037 / 60000000000000000 : ℚ),
    (-101673746728037 / 20000000000000000 : ℚ),
    (101673746728037 / 20000000000000000 : ℚ),
    (-101673746728037 / 60000000000000000 : ℚ)
  ],
  ![
    (-101673746728037 / 20000000000000000 : ℚ),
    (305021240184111 / 20000000000000000 : ℚ),
    (-305021240184111 / 20000000000000000 : ℚ),
    (101673746728037 / 20000000000000000 : ℚ)
  ],
  ![
    (101673746728037 / 20000000000000000 : ℚ),
    (-305021240184111 / 20000000000000000 : ℚ),
    (305021240184111 / 20000000000000000 : ℚ),
    (-101673746728037 / 20000000000000000 : ℚ)
  ],
  ![
    (-101673746728037 / 60000000000000000 : ℚ),
    (101673746728037 / 20000000000000000 : ℚ),
    (-101673746728037 / 20000000000000000 : ℚ),
    (101673746728037 / 60000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_21_5_correct (a b : Fin 4) :
    correctionCellCoefficient 21 5 a b = cellMatrix_21_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 21 5 a.val b.val = cellMatrix_21_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (21, 6). -/
def cellMatrix_21_6 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_21_6_correct (a b : Fin 4) :
    correctionCellCoefficient 21 6 a b = cellMatrix_21_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 21 6 a.val b.val = cellMatrix_21_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (22, 0). -/
def cellMatrix_22_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (55615323361648541 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-729094242524039 / 150000000000000000 : ℚ),
    (-1069868166119 / 180000000000000000 : ℚ)
  ],
  ![
    (-1007236919590597 / 60000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (44306293896371 / 50000000000000000 : ℚ),
    (-1006576656610901 / 300000000000000000 : ℚ)
  ],
  ![
    (-572085568406557 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (151350521208767 / 25000000000000000 : ℚ),
    (-27884258457031 / 4687500000000000 : ℚ)
  ],
  ![
    (70303869253957 / 90000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1449555276103507 / 150000000000000000 : ℚ),
    (199851653897073 / 25000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_22_0_correct (a b : Fin 4) :
    correctionCellCoefficient 22 0 a b = cellMatrix_22_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 22 0 a.val b.val = cellMatrix_22_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (22, 1). -/
def cellMatrix_22_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (3202213035354607 / 56250000000000000 : ℚ),
    (-973908770308917 / 100000000000000000 : ℚ),
    (-1463537825878673 / 300000000000000000 : ℚ),
    (-3131322168636773 / 1800000000000000000 : ℚ)
  ],
  ![
    (-288846174559283 / 15000000000000000 : ℚ),
    (-829351481025417 / 100000000000000000 : ℚ),
    (-917964068818159 / 100000000000000000 : ℚ),
    (4212823008266809 / 600000000000000000 : ℚ)
  ],
  ![
    (-540471855151337 / 300000000000000000 : ℚ),
    (-71723546447481 / 12500000000000000 : ℚ),
    (-294797614103729 / 25000000000000000 : ℚ),
    (1677764347648799 / 120000000000000000 : ℚ)
  ],
  ![
    (-199908355946711 / 225000000000000000 : ℚ),
    (6982192179403 / 1500000000000000 : ℚ),
    (2147774494043807 / 150000000000000000 : ℚ),
    (-10507034028332999 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_22_1_correct (a b : Fin 4) :
    correctionCellCoefficient 22 1 a b = cellMatrix_22_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 22 1 a.val b.val = cellMatrix_22_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (22, 2). -/
def cellMatrix_22_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (24342636713959369 / 600000000000000000 : ℚ),
    (-14828926094004967 / 600000000000000000 : ℚ),
    (-2019465940131373 / 200000000000000000 : ℚ),
    (2294111734624639 / 300000000000000000 : ℚ)
  ],
  ![
    (-17824917273165967 / 600000000000000000 : ℚ),
    (-1117736229056661 / 200000000000000000 : ℚ),
    (2376894870630491 / 200000000000000000 : ℚ),
    (-134542410785789 / 300000000000000000 : ℚ)
  ],
  ![
    (-1069998313342421 / 200000000000000000 : ℚ),
    (504896633884927 / 40000000000000000 : ℚ),
    (6030440825414163 / 200000000000000000 : ℚ),
    (-434843073089313 / 20000000000000000 : ℚ)
  ],
  ![
    (5769294819784799 / 900000000000000000 : ℚ),
    (-519497616277171 / 300000000000000000 : ℚ),
    (-1242297008049077 / 60000000000000000 : ℚ),
    (3648557017809859 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_22_2_correct (a b : Fin 4) :
    correctionCellCoefficient 22 2 a b = cellMatrix_22_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 22 2 a.val b.val = cellMatrix_22_2 a b) a b

end PartialBalayage.Maximal.Square
