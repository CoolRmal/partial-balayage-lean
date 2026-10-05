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

/-- Candidate finite rational coefficient matrix on cell (14, 3). -/
def cellMatrix_14_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (455544990414047 / 3515625000000000 : ℚ),
    (635222537132123 / 60000000000000000 : ℚ),
    (19178752153447 / 37500000000000000 : ℚ),
    (-702459649931099 / 900000000000000000 : ℚ)
  ],
  ![
    (1789560318508037 / 300000000000000000 : ℚ),
    (-142751841526777 / 50000000000000000 : ℚ),
    (-64057940363521 / 100000000000000000 : ℚ),
    (2735606903337 / 20000000000000000 : ℚ)
  ],
  ![
    (-128415714897461 / 37500000000000000 : ℚ),
    (1203314109379 / 100000000000000000 : ℚ),
    (116513180153 / 2500000000000000 : ℚ),
    (-6803981460113 / 300000000000000000 : ℚ)
  ],
  ![
    (45034058365541 / 200000000000000000 : ℚ),
    (-2921902231007 / 120000000000000000 : ℚ),
    (-1078551634379 / 200000000000000000 : ℚ),
    (-7103680887059 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_3_correct (a b : Fin 4) :
    correctionCellCoefficient 14 3 a b = cellMatrix_14_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 3 a.val b.val = cellMatrix_14_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 4). -/
def cellMatrix_14_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (20984281000788251 / 150000000000000000 : ℚ),
    (231709422515389 / 25000000000000000 : ℚ),
    (-183009877567841 / 100000000000000000 : ℚ),
    (-1501369062104021 / 1800000000000000000 : ℚ)
  ],
  ![
    (781909551806867 / 300000000000000000 : ℚ),
    (-372585460230541 / 100000000000000000 : ℚ),
    (-11511918406733 / 50000000000000000 : ℚ),
    (31018930612903 / 200000000000000000 : ℚ)
  ],
  ![
    (-42355757362221 / 12500000000000000 : ℚ),
    (1860193530753 / 50000000000000000 : ℚ),
    (-2143454253993 / 100000000000000000 : ℚ),
    (-44287968784043 / 600000000000000000 : ℚ)
  ],
  ![
    (67512733068247 / 360000000000000000 : ℚ),
    (-35288182735427 / 600000000000000000 : ℚ),
    (-3488603335451 / 120000000000000000 : ℚ),
    (67061911350583 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_4_correct (a b : Fin 4) :
    correctionCellCoefficient 14 4 a b = cellMatrix_14_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 4 a.val b.val = cellMatrix_14_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 5). -/
def cellMatrix_14_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (263698903572241861 / 1800000000000000000 : ℚ),
    (1863538547451223 / 600000000000000000 : ℚ),
    (-2599428327511067 / 600000000000000000 : ℚ),
    (-99745138446493 / 600000000000000000 : ℚ)
  ],
  ![
    (-716779886811599 / 600000000000000000 : ℚ),
    (-744209475876237 / 200000000000000000 : ℚ),
    (47009118211777 / 200000000000000000 : ℚ),
    (9087194638601 / 120000000000000000 : ℚ)
  ],
  ![
    (-2067902725325573 / 600000000000000000 : ℚ),
    (-45421011677003 / 200000000000000000 : ℚ),
    (-48574877292029 / 200000000000000000 : ℚ),
    (15697260279071 / 200000000000000000 : ℚ)
  ],
  ![
    (6845332734827 / 50000000000000000 : ℚ),
    (-518717456559 / 100000000000000000 : ℚ),
    (1033726972361 / 12500000000000000 : ℚ),
    (-17029992999017 / 120000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_5_correct (a b : Fin 4) :
    correctionCellCoefficient 14 5 a b = cellMatrix_14_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 5 a.val b.val = cellMatrix_14_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 6). -/
def cellMatrix_14_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (5223839976334457 / 36000000000000000 : ℚ),
    (-121151784097013 / 20000000000000000 : ℚ),
    (-1449331871425273 / 300000000000000000 : ℚ),
    (130546463341 / 450000000000000000 : ℚ)
  ],
  ![
    (-1381472493305987 / 300000000000000000 : ℚ),
    (-302377633129839 / 100000000000000000 : ℚ),
    (46222545702391 / 100000000000000000 : ℚ),
    (-10711352538151 / 60000000000000000 : ℚ)
  ],
  ![
    (-17990614151527 / 4687500000000000 : ℚ),
    (-11934873177981 / 25000000000000000 : ℚ),
    (-46346764213 / 6250000000000000 : ℚ),
    (-16926120752831 / 37500000000000000 : ℚ)
  ],
  ![
    (43500617756813 / 600000000000000000 : ℚ),
    (-53108136792651 / 200000000000000000 : ℚ),
    (-68610333437309 / 200000000000000000 : ℚ),
    (19016051905049 / 37500000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_6_correct (a b : Fin 4) :
    correctionCellCoefficient 14 6 a b = cellMatrix_14_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 6 a.val b.val = cellMatrix_14_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 7). -/
def cellMatrix_14_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (120796434602646703 / 900000000000000000 : ℚ),
    (-1571893137126353 / 100000000000000000 : ℚ),
    (-1449070778498591 / 300000000000000000 : ℚ),
    (-113395859962151 / 600000000000000000 : ℚ)
  ],
  ![
    (-1101747259139543 / 150000000000000000 : ℚ),
    (-65872326103953 / 25000000000000000 : ℚ),
    (-1833554247091 / 25000000000000000 : ℚ),
    (436729252148359 / 600000000000000000 : ℚ)
  ],
  ![
    (-358062848634593 / 75000000000000000 : ℚ),
    (-46157888797347 / 25000000000000000 : ℚ),
    (-17018814281257 / 12500000000000000 : ℚ),
    (242780724774913 / 200000000000000000 : ℚ)
  ],
  ![
    (-17397962452283 / 600000000000000000 : ℚ),
    (22785605362703 / 40000000000000000 : ℚ),
    (9425859881739 / 8000000000000000 : ℚ),
    (-3842092751068021 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_7_correct (a b : Fin 4) :
    correctionCellCoefficient 14 7 a b = cellMatrix_14_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 7 a.val b.val = cellMatrix_14_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 8). -/
def cellMatrix_14_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (204264180486141053 / 1800000000000000000 : ℚ),
    (-3113565903327787 / 120000000000000000 : ℚ),
    (-647665827376727 / 120000000000000000 : ℚ),
    (9117227461583 / 200000000000000000 : ℚ)
  ],
  ![
    (-5595200912834869 / 600000000000000000 : ℚ),
    (-119586224636721 / 200000000000000000 : ℚ),
    (422060818171631 / 200000000000000000 : ℚ),
    (-1609891575030197 / 600000000000000000 : ℚ)
  ],
  ![
    (-4060853031388669 / 600000000000000000 : ℚ),
    (-185522993054261 / 200000000000000000 : ℚ),
    (456041145824627 / 200000000000000000 : ℚ),
    (-1150684451649471 / 200000000000000000 : ℚ)
  ],
  ![
    (-18702898092799 / 45000000000000000 : ℚ),
    (-1043214844183313 / 300000000000000000 : ℚ),
    (-783788314984399 / 150000000000000000 : ℚ),
    (4706825946761123 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_8_correct (a b : Fin 4) :
    correctionCellCoefficient 14 8 a b = cellMatrix_14_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 8 a.val b.val = cellMatrix_14_8 a b) a b

end PartialBalayage.Maximal.Square
