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

/-- Candidate finite rational coefficient matrix on cell (23, 3). -/
def cellMatrix_23_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (2453520659103157 / 1800000000000000000 : ℚ),
    (-2453520659103157 / 600000000000000000 : ℚ),
    (2453520659103157 / 600000000000000000 : ℚ),
    (-2453520659103157 / 1800000000000000000 : ℚ)
  ],
  ![
    (-2453520659103157 / 600000000000000000 : ℚ),
    (2453520659103157 / 200000000000000000 : ℚ),
    (-2453520659103157 / 200000000000000000 : ℚ),
    (2453520659103157 / 600000000000000000 : ℚ)
  ],
  ![
    (2453520659103157 / 600000000000000000 : ℚ),
    (-2453520659103157 / 200000000000000000 : ℚ),
    (2453520659103157 / 200000000000000000 : ℚ),
    (-2453520659103157 / 600000000000000000 : ℚ)
  ],
  ![
    (-2453520659103157 / 1800000000000000000 : ℚ),
    (2453520659103157 / 600000000000000000 : ℚ),
    (-2453520659103157 / 600000000000000000 : ℚ),
    (2453520659103157 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_23_3_correct (a b : Fin 4) :
    correctionCellCoefficient 23 3 a b = cellMatrix_23_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 23 3 a.val b.val = cellMatrix_23_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (23, 4). -/
def cellMatrix_23_4 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_23_4_correct (a b : Fin 4) :
    correctionCellCoefficient 23 4 a b = cellMatrix_23_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 23 4 a.val b.val = cellMatrix_23_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (24, 0). -/
def cellMatrix_24_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (5527359380740007 / 225000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-3885713325449297 / 150000000000000000 : ℚ),
    (10562709272820751 / 900000000000000000 : ℚ)
  ],
  ![
    (-1640108267957353 / 75000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1537787333357 / 50000000000000000 : ℚ),
    (1099044065527211 / 300000000000000000 : ℚ)
  ],
  ![
    (-151758644216987 / 37500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (486290835931171 / 12500000000000000 : ℚ),
    (-866240091837649 / 37500000000000000 : ℚ)
  ],
  ![
    (102026405330371 / 18000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1166790448768139 / 60000000000000000 : ℚ),
    (3938143627715273 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_24_0_correct (a b : Fin 4) :
    correctionCellCoefficient 24 0 a b = cellMatrix_24_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 24 0 a.val b.val = cellMatrix_24_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (24, 1). -/
def cellMatrix_24_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (3119288947694999 / 300000000000000000 : ℚ),
    (-4980144028976437 / 300000000000000000 : ℚ),
    (930427540640719 / 100000000000000000 : ℚ),
    (-1696851918395017 / 900000000000000000 : ℚ)
  ],
  ![
    (-5470615730302343 / 300000000000000000 : ℚ),
    (1092892916193783 / 100000000000000000 : ℚ),
    (1095968490860497 / 100000000000000000 : ℚ),
    (-730133064795879 / 100000000000000000 : ℚ)
  ],
  ![
    (146957923912959 / 12500000000000000 : ℚ),
    (106341580024693 / 12500000000000000 : ℚ),
    (-189974627953239 / 6250000000000000 : ℚ),
    (1033506187694741 / 75000000000000000 : ℚ)
  ],
  ![
    (-1022070958286141 / 360000000000000000 : ℚ),
    (-243006055785761 / 40000000000000000 : ℚ),
    (320912546035799 / 24000000000000000 : ℚ),
    (-680778337196617 / 120000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_24_1_correct (a b : Fin 4) :
    correctionCellCoefficient 24 1 a b = cellMatrix_24_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 24 1 a.val b.val = cellMatrix_24_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (24, 2). -/
def cellMatrix_24_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (54721535176357 / 45000000000000000 : ℚ),
    (-54721535176357 / 15000000000000000 : ℚ),
    (54721535176357 / 15000000000000000 : ℚ),
    (-54721535176357 / 45000000000000000 : ℚ)
  ],
  ![
    (-54721535176357 / 15000000000000000 : ℚ),
    (54721535176357 / 5000000000000000 : ℚ),
    (-54721535176357 / 5000000000000000 : ℚ),
    (54721535176357 / 15000000000000000 : ℚ)
  ],
  ![
    (54721535176357 / 15000000000000000 : ℚ),
    (-54721535176357 / 5000000000000000 : ℚ),
    (54721535176357 / 5000000000000000 : ℚ),
    (-54721535176357 / 15000000000000000 : ℚ)
  ],
  ![
    (-54721535176357 / 45000000000000000 : ℚ),
    (54721535176357 / 15000000000000000 : ℚ),
    (-54721535176357 / 15000000000000000 : ℚ),
    (54721535176357 / 45000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_24_2_correct (a b : Fin 4) :
    correctionCellCoefficient 24 2 a b = cellMatrix_24_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 24 2 a.val b.val = cellMatrix_24_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (24, 3). -/
def cellMatrix_24_3 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_24_3_correct (a b : Fin 4) :
    correctionCellCoefficient 24 3 a b = cellMatrix_24_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 24 3 a.val b.val = cellMatrix_24_3 a b) a b

end PartialBalayage.Maximal.Square
