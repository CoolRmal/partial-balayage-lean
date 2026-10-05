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

/-- Candidate finite rational coefficient matrix on cell (11, 6). -/
def cellMatrix_11_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (233740920119426459 / 1800000000000000000 : ℚ),
    (103052202399821 / 40000000000000000 : ℚ),
    (-4708576494038347 / 600000000000000000 : ℚ),
    (-344192056094033 / 600000000000000000 : ℚ)
  ],
  ![
    (5888939538060299 / 600000000000000000 : ℚ),
    (-1178330189206797 / 200000000000000000 : ℚ),
    (233961774448061 / 200000000000000000 : ℚ),
    (65143413820013 / 600000000000000000 : ℚ)
  ],
  ![
    (642591567841511 / 600000000000000000 : ℚ),
    (525770813254143 / 200000000000000000 : ℚ),
    (25833532664957 / 200000000000000000 : ℚ),
    (71688922365419 / 200000000000000000 : ℚ)
  ],
  ![
    (-1877971340046169 / 1800000000000000000 : ℚ),
    (-378421090255193 / 600000000000000000 : ℚ),
    (-5277607397969 / 120000000000000000 : ℚ),
    (-5061957955181 / 28125000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_6_correct (a b : Fin 4) :
    correctionCellCoefficient 11 6 a b = cellMatrix_11_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 6 a.val b.val = cellMatrix_11_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 7). -/
def cellMatrix_11_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (13951247723563829 / 112500000000000000 : ℚ),
    (-4451973060180739 / 300000000000000000 : ℚ),
    (-2870576331160223 / 300000000000000000 : ℚ),
    (-1727439734770807 / 900000000000000000 : ℚ)
  ],
  ![
    (390122213450513 / 75000000000000000 : ℚ),
    (-322631613245331 / 100000000000000000 : ℚ),
    (149552594134037 / 100000000000000000 : ℚ),
    (285891100481423 / 300000000000000000 : ℚ)
  ],
  ![
    (628117843173767 / 150000000000000000 : ℚ),
    (396252322840157 / 100000000000000000 : ℚ),
    (120450149880607 / 100000000000000000 : ℚ),
    (-2193958103873 / 150000000000000000 : ℚ)
  ],
  ![
    (-379596003434763 / 200000000000000000 : ℚ),
    (-251720824455489 / 200000000000000000 : ℚ),
    (-116784448707143 / 200000000000000000 : ℚ),
    (-12161761224517 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_7_correct (a b : Fin 4) :
    correctionCellCoefficient 11 7 a b = cellMatrix_11_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 7 a.val b.val = cellMatrix_11_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 8). -/
def cellMatrix_11_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (9768321542190771 / 100000000000000000 : ℚ),
    (-496690227386333 / 12500000000000000 : ℚ),
    (-153267202197701 / 10000000000000000 : ℚ),
    (-14608912499765459 / 1800000000000000000 : ℚ)
  ],
  ![
    (1327142896949593 / 300000000000000000 : ℚ),
    (131182337752083 / 50000000000000000 : ℚ),
    (21772184730773 / 5000000000000000 : ℚ),
    (1615148716391767 / 200000000000000000 : ℚ)
  ],
  ![
    (729675830287 / 78125000000000 : ℚ),
    (5062117651149 / 800000000000000 : ℚ),
    (116062233672861 / 100000000000000000 : ℚ),
    (-1576350570985169 / 600000000000000000 : ℚ)
  ],
  ![
    (-421567078162567 / 112500000000000000 : ℚ),
    (-734015463416921 / 300000000000000000 : ℚ),
    (-181257553672973 / 300000000000000000 : ℚ),
    (73642912324877 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_8_correct (a b : Fin 4) :
    correctionCellCoefficient 11 8 a b = cellMatrix_11_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 8 a.val b.val = cellMatrix_11_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 9). -/
def cellMatrix_11_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (62109386120450287 / 1800000000000000000 : ℚ),
    (-56842107678033563 / 600000000000000000 : ℚ),
    (-23804944631627519 / 600000000000000000 : ℚ),
    (-3002133999351597 / 200000000000000000 : ℚ)
  ],
  ![
    (11686582163792243 / 600000000000000000 : ℚ),
    (7111950278645473 / 200000000000000000 : ℚ),
    (5716333538406221 / 200000000000000000 : ℚ),
    (-19810660560079211 / 600000000000000000 : ℚ)
  ],
  ![
    (8520521446017907 / 600000000000000000 : ℚ),
    (6137111059741 / 8000000000000000 : ℚ),
    (-1344226103639447 / 200000000000000000 : ℚ),
    (15177957621627763 / 200000000000000000 : ℚ)
  ],
  ![
    (-2014904254748447 / 300000000000000000 : ℚ),
    (-102288765843799 / 30000000000000000 : ℚ),
    (-70061615461 / 195312500000000 : ℚ),
    (-9775468355960687 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_9_correct (a b : Fin 4) :
    correctionCellCoefficient 11 9 a b = cellMatrix_11_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 9 a.val b.val = cellMatrix_11_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 10). -/
def cellMatrix_11_10 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-51712744200674333 / 450000000000000000 : ℚ),
    (-21911867155908829 / 100000000000000000 : ℚ),
    (-12706037656447973 / 150000000000000000 : ℚ),
    (225998219998453621 / 1800000000000000000 : ℚ)
  ],
  ![
    (5060128842478019 / 100000000000000000 : ℚ),
    (-79127700288831 / 12500000000000000 : ℚ),
    (-1409432702167299 / 20000000000000000 : ℚ),
    (2866351145143869 / 200000000000000000 : ℚ)
  ],
  ![
    (5048199932946343 / 60000000000000000 : ℚ),
    (33592850339139 / 156250000000000 : ℚ),
    (22094823380621921 / 100000000000000000 : ℚ),
    (-136873415542826987 / 600000000000000000 : ℚ)
  ],
  ![
    (-646043745524761 / 15000000000000000 : ℚ),
    (-30564522009016243 / 300000000000000000 : ℚ),
    (-9811339903076719 / 100000000000000000 : ℚ),
    (11616337916029839 / 100000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_10_correct (a b : Fin 4) :
    correctionCellCoefficient 11 10 a b = cellMatrix_11_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 10 a.val b.val = cellMatrix_11_10 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 11). -/
def cellMatrix_11_11 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-527738817487978309 / 1800000000000000000 : ℚ),
    (-2373761396194379 / 200000000000000000 : ℚ),
    (175174069372661729 / 600000000000000000 : ℚ),
    (-12690134293550701 / 100000000000000000 : ℚ)
  ],
  ![
    (-2373761396194379 / 200000000000000000 : ℚ),
    (-20855643812535669 / 200000000000000000 : ℚ),
    (-5495273586241383 / 200000000000000000 : ℚ),
    (7557239908395997 / 150000000000000000 : ℚ)
  ],
  ![
    (175174069372661729 / 600000000000000000 : ℚ),
    (-5495273586241383 / 200000000000000000 : ℚ),
    (-18536753756316629 / 40000000000000000 : ℚ),
    (12518836922506399 / 50000000000000000 : ℚ)
  ],
  ![
    (-12690134293550701 / 100000000000000000 : ℚ),
    (7557239908395997 / 150000000000000000 : ℚ),
    (12518836922506399 / 50000000000000000 : ℚ),
    (-90879386636130617 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_11_correct (a b : Fin 4) :
    correctionCellCoefficient 11 11 a b = cellMatrix_11_11 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 11 a.val b.val = cellMatrix_11_11 a b) a b

end PartialBalayage.Maximal.Square
