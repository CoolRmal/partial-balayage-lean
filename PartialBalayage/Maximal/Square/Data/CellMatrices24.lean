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

/-- Candidate finite rational coefficient matrix on cell (17, 0). -/
def cellMatrix_17_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (2102736118896631 / 18000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (11288054602591 / 60000000000000000 : ℚ),
    (351414036759887 / 900000000000000000 : ℚ)
  ],
  ![
    (-90341271693847 / 18750000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1928184089129 / 20000000000000000 : ℚ),
    (-20950129773497 / 100000000000000000 : ℚ)
  ],
  ![
    (-4549922776783 / 3000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-30895924793551 / 100000000000000000 : ℚ),
    (22238596767313 / 150000000000000000 : ℚ)
  ],
  ![
    (11075110010261 / 180000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (15317732830121 / 150000000000000000 : ℚ),
    (-3301958672851 / 50000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_0_correct (a b : Fin 4) :
    correctionCellCoefficient 17 0 a b = cellMatrix_17_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 0 a.val b.val = cellMatrix_17_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 1). -/
def cellMatrix_17_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (52828770400315151 / 450000000000000000 : ℚ),
    (154764860928599 / 100000000000000000 : ℚ),
    (203927154886421 / 150000000000000000 : ℚ),
    (-874842803842831 / 1800000000000000000 : ℚ)
  ],
  ![
    (-768616748879489 / 150000000000000000 : ℚ),
    (-82132230211781 / 100000000000000000 : ℚ),
    (-9061413720767 / 12500000000000000 : ℚ),
    (3293814178483 / 200000000000000000 : ℚ)
  ],
  ![
    (-503202858524327 / 300000000000000000 : ℚ),
    (-4328664013119 / 25000000000000000 : ℚ),
    (543250749643 / 4000000000000000 : ℚ),
    (-53594930027107 / 600000000000000000 : ℚ)
  ],
  ![
    (87846690920713 / 900000000000000000 : ℚ),
    (917837604583 / 150000000000000000 : ℚ),
    (-7199947612769 / 75000000000000000 : ℚ),
    (100299143721481 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_1_correct (a b : Fin 4) :
    correctionCellCoefficient 17 1 a b = cellMatrix_17_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 1 a.val b.val = cellMatrix_17_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 2). -/
def cellMatrix_17_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (215673132152769607 / 1800000000000000000 : ℚ),
    (561721200273377 / 200000000000000000 : ℚ),
    (-59134184297147 / 600000000000000000 : ℚ),
    (-369275771274739 / 900000000000000000 : ℚ)
  ],
  ![
    (-3992326792850009 / 600000000000000000 : ℚ),
    (-444348256952657 / 200000000000000000 : ℚ),
    (-135101176996823 / 200000000000000000 : ℚ),
    (102160505029 / 15000000000000000 : ℚ)
  ],
  ![
    (-1082400970944167 / 600000000000000000 : ℚ),
    (-33899167167759 / 200000000000000000 : ℚ),
    (-26432392544957 / 200000000000000000 : ℚ),
    (19697165189567 / 300000000000000000 : ℚ)
  ],
  ![
    (38069278037149 / 600000000000000000 : ℚ),
    (-3742889221497 / 200000000000000000 : ℚ),
    (14233187606443 / 200000000000000000 : ℚ),
    (-186578084352841 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_2_correct (a b : Fin 4) :
    correctionCellCoefficient 17 2 a b = cellMatrix_17_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 2 a.val b.val = cellMatrix_17_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 3). -/
def cellMatrix_17_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (219812668859789081 / 1800000000000000000 : ℚ),
    (276114563225453 / 200000000000000000 : ℚ),
    (-6381485814773 / 4800000000000000 : ℚ),
    (-1126396651192279 / 1800000000000000000 : ℚ)
  ],
  ![
    (-5726588674497289 / 600000000000000000 : ℚ),
    (-710464190745143 / 200000000000000000 : ℚ),
    (-131014756795663 / 200000000000000000 : ℚ),
    (-102154082256787 / 600000000000000000 : ℚ)
  ],
  ![
    (-1224001319703181 / 600000000000000000 : ℚ),
    (-47369621878539 / 200000000000000000 : ℚ),
    (12961937834177 / 200000000000000000 : ℚ),
    (-163753707803407 / 600000000000000000 : ℚ)
  ],
  ![
    (275530440289 / 22500000000000000 : ℚ),
    (-56203813189337 / 300000000000000000 : ℚ),
    (-17984815191689 / 75000000000000000 : ℚ),
    (110440995485249 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_3_correct (a b : Fin 4) :
    correctionCellCoefficient 17 3 a b = cellMatrix_17_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 3 a.val b.val = cellMatrix_17_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 4). -/
def cellMatrix_17_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (54694561524271501 / 450000000000000000 : ℚ),
    (-63114147173639 / 20000000000000000 : ℚ),
    (-240510297254863 / 75000000000000000 : ℚ),
    (-1212964222323803 / 1800000000000000000 : ℚ)
  ],
  ![
    (-4176589799688247 / 300000000000000000 : ℚ),
    (-134330973324157 / 25000000000000000 : ℚ),
    (-4663376781049 / 4000000000000000 : ℚ),
    (104791650807269 / 200000000000000000 : ℚ)
  ],
  ![
    (-745489039819837 / 300000000000000000 : ℚ),
    (-23149931751699 / 25000000000000000 : ℚ),
    (-15079176996923 / 20000000000000000 : ℚ),
    (564132289998241 / 600000000000000000 : ℚ)
  ],
  ![
    (-10521254450243 / 225000000000000000 : ℚ),
    (21873441955483 / 50000000000000000 : ℚ),
    (259383725688991 / 300000000000000000 : ℚ),
    (-369268295507237 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_4_correct (a b : Fin 4) :
    correctionCellCoefficient 17 4 a b = cellMatrix_17_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 4 a.val b.val = cellMatrix_17_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 5). -/
def cellMatrix_17_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (206112761495017979 / 1800000000000000000 : ℚ),
    (-2318184464536927 / 200000000000000000 : ℚ),
    (-3137046600362707 / 600000000000000000 : ℚ),
    (-724117916541199 / 900000000000000000 : ℚ)
  ],
  ![
    (-2392450904778361 / 120000000000000000 : ℚ),
    (-1226610512276349 / 200000000000000000 : ℚ),
    (81206113369357 / 200000000000000000 : ℚ),
    (-1034668963980743 / 300000000000000000 : ℚ)
  ],
  ![
    (-1934819461589899 / 600000000000000000 : ℚ),
    (77349296046189 / 200000000000000000 : ℚ),
    (413340520029011 / 200000000000000000 : ℚ),
    (-90641989182589 / 18750000000000000 : ℚ)
  ],
  ![
    (-1063838430635743 / 1800000000000000000 : ℚ),
    (-2023398453343373 / 600000000000000000 : ℚ),
    (-2804647208187151 / 600000000000000000 : ℚ),
    (6747378935996557 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_5_correct (a b : Fin 4) :
    correctionCellCoefficient 17 5 a b = cellMatrix_17_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 5 a.val b.val = cellMatrix_17_5 a b) a b

end PartialBalayage.Maximal.Square
