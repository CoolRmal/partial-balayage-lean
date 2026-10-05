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

/-- Candidate finite rational coefficient matrix on cell (15, 1). -/
def cellMatrix_15_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (216043301787291733 / 1800000000000000000 : ℚ),
    (553222570115339 / 200000000000000000 : ℚ),
    (1597241578317013 / 600000000000000000 : ℚ),
    (-460109036303 / 937500000000000 : ℚ)
  ],
  ![
    (1854669552400399 / 600000000000000000 : ℚ),
    (-80412364522409 / 200000000000000000 : ℚ),
    (-110658082191749 / 200000000000000000 : ℚ),
    (-6963447865159 / 150000000000000000 : ℚ)
  ],
  ![
    (-1540819645387883 / 600000000000000000 : ℚ),
    (-33153347073207 / 200000000000000000 : ℚ),
    (19857110682517 / 200000000000000000 : ℚ),
    (-3725522284977 / 100000000000000000 : ℚ)
  ],
  ![
    (174932026323487 / 900000000000000000 : ℚ),
    (2511862871171 / 60000000000000000 : ℚ),
    (-7566150429389 / 75000000000000000 : ℚ),
    (79194782576389 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_1_correct (a b : Fin 4) :
    correctionCellCoefficient 15 1 a b = cellMatrix_15_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 1 a.val b.val = cellMatrix_15_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 2). -/
def cellMatrix_15_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (224930620303579063 / 1800000000000000000 : ℚ),
    (3970741517278283 / 600000000000000000 : ℚ),
    (713832228615253 / 600000000000000000 : ℚ),
    (-63882694000637 / 150000000000000000 : ℚ)
  ],
  ![
    (417868140265763 / 200000000000000000 : ℚ),
    (-329582320366543 / 200000000000000000 : ℚ),
    (-27702374730477 / 40000000000000000 : ℚ),
    (4300407807781 / 100000000000000000 : ℚ)
  ],
  ![
    (-320612297653963 / 120000000000000000 : ℚ),
    (-3158451883607 / 40000000000000000 : ℚ),
    (-499204605469 / 40000000000000000 : ℚ),
    (11173727261 / 781250000000000 : ℚ)
  ],
  ![
    (107609037017719 / 600000000000000000 : ℚ),
    (-133959964657 / 4800000000000000 : ℚ),
    (6221859713759 / 200000000000000000 : ℚ),
    (-7237885386167 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_2_correct (a b : Fin 4) :
    correctionCellCoefficient 15 2 a b = cellMatrix_15_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 2 a.val b.val = cellMatrix_15_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 3). -/
def cellMatrix_15_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (238217749213252027 / 1800000000000000000 : ℚ),
    (926362729300229 / 120000000000000000 : ℚ),
    (-52760099392391 / 600000000000000000 : ℚ),
    (-151718241137083 / 225000000000000000 : ℚ)
  ],
  ![
    (-41625238137603 / 200000000000000000 : ℚ),
    (-580803620824627 / 200000000000000000 : ℚ),
    (-112709426805699 / 200000000000000000 : ℚ),
    (677415324759 / 10000000000000000 : ℚ)
  ],
  ![
    (-1649344913069507 / 600000000000000000 : ℚ),
    (-12202882936277 / 200000000000000000 : ℚ),
    (6085399509103 / 200000000000000000 : ℚ),
    (-3476915586793 / 75000000000000000 : ℚ)
  ],
  ![
    (95053849804537 / 600000000000000000 : ℚ),
    (-22841149616573 / 600000000000000000 : ℚ),
    (-330156442343 / 8000000000000000 : ℚ),
    (725004723223 / 25000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_3_correct (a b : Fin 4) :
    correctionCellCoefficient 15 3 a b = cellMatrix_15_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 3 a.val b.val = cellMatrix_15_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 4). -/
def cellMatrix_15_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (2005929311403853 / 14400000000000000 : ℚ),
    (3312547518619699 / 600000000000000000 : ℚ),
    (-253301205697811 / 120000000000000000 : ℚ),
    (-4025002129967 / 5625000000000000 : ℚ)
  ],
  ![
    (-721589979272749 / 200000000000000000 : ℚ),
    (-153115510990097 / 40000000000000000 : ℚ),
    (-72064507320159 / 200000000000000000 : ℚ),
    (11923794270201 / 100000000000000000 : ℚ)
  ],
  ![
    (-1695512688045373 / 600000000000000000 : ℚ),
    (-5569481722483 / 40000000000000000 : ℚ),
    (-21729925185241 / 200000000000000000 : ℚ),
    (1138697128327 / 30000000000000000 : ℚ)
  ],
  ![
    (64851080369591 / 600000000000000000 : ℚ),
    (-20164275895967 / 600000000000000000 : ℚ),
    (9146202298777 / 200000000000000000 : ℚ),
    (-19481096544863 / 180000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_4_correct (a b : Fin 4) :
    correctionCellCoefficient 15 4 a b = cellMatrix_15_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 4 a.val b.val = cellMatrix_15_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 5). -/
def cellMatrix_15_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (255591287714284117 / 1800000000000000000 : ℚ),
    (-508465219947851 / 600000000000000000 : ℚ),
    (-510901342015699 / 120000000000000000 : ℚ),
    (-577295933821 / 3750000000000000 : ℚ)
  ],
  ![
    (-1535384453002991 / 200000000000000000 : ℚ),
    (-838163803969597 / 200000000000000000 : ℚ),
    (-521741698953 / 200000000000000000 : ℚ),
    (-1809849376841 / 9375000000000000 : ℚ)
  ],
  ![
    (-1821470746871801 / 600000000000000000 : ℚ),
    (-48533316416357 / 200000000000000000 : ℚ),
    (1044017381299 / 200000000000000000 : ℚ),
    (-34726352358007 / 100000000000000000 : ℚ)
  ],
  ![
    (4313053732247 / 360000000000000000 : ℚ),
    (-32019605510387 / 120000000000000000 : ℚ),
    (-167372358552299 / 600000000000000000 : ℚ),
    (32752300592569 / 75000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_5_correct (a b : Fin 4) :
    correctionCellCoefficient 15 5 a b = cellMatrix_15_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 5 a.val b.val = cellMatrix_15_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 6). -/
def cellMatrix_15_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (246125269875970999 / 1800000000000000000 : ℚ),
    (-1964860229446307 / 200000000000000000 : ℚ),
    (-113264350332503 / 24000000000000000 : ℚ),
    (-110250847492351 / 900000000000000000 : ℚ)
  ],
  ![
    (-7238040356132447 / 600000000000000000 : ℚ),
    (-955037647485327 / 200000000000000000 : ℚ),
    (-116352101816777 / 200000000000000000 : ℚ),
    (1056084407881 / 2400000000000000 : ℚ)
  ],
  ![
    (-2172296758125017 / 600000000000000000 : ℚ),
    (-254803395801801 / 200000000000000000 : ℚ),
    (-207314096766743 / 200000000000000000 : ℚ),
    (10030508740579 / 9375000000000000 : ℚ)
  ],
  ![
    (-174790675429811 / 1800000000000000000 : ℚ),
    (291212469565123 / 600000000000000000 : ℚ),
    (618682855669357 / 600000000000000000 : ℚ),
    (-1793646539089237 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_6_correct (a b : Fin 4) :
    correctionCellCoefficient 15 6 a b = cellMatrix_15_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 6 a.val b.val = cellMatrix_15_6 a b) a b

end PartialBalayage.Maximal.Square
