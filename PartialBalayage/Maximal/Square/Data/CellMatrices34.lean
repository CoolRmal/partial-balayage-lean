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

/-- Candidate finite rational coefficient matrix on cell (25, 0). -/
def cellMatrix_25_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (1943625556391327 / 450000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1943625556391327 / 300000000000000000 : ℚ),
    (1943625556391327 / 600000000000000000 : ℚ)
  ],
  ![
    (-1943625556391327 / 150000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (1943625556391327 / 100000000000000000 : ℚ),
    (-1943625556391327 / 200000000000000000 : ℚ)
  ],
  ![
    (1943625556391327 / 150000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1943625556391327 / 100000000000000000 : ℚ),
    (1943625556391327 / 200000000000000000 : ℚ)
  ],
  ![
    (-1943625556391327 / 450000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (1943625556391327 / 300000000000000000 : ℚ),
    (-1943625556391327 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_25_0_correct (a b : Fin 4) :
    correctionCellCoefficient 25 0 a b = cellMatrix_25_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 25 0 a.val b.val = cellMatrix_25_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (25, 1). -/
def cellMatrix_25_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (1943625556391327 / 1800000000000000000 : ℚ),
    (-1943625556391327 / 600000000000000000 : ℚ),
    (1943625556391327 / 600000000000000000 : ℚ),
    (-1943625556391327 / 1800000000000000000 : ℚ)
  ],
  ![
    (-1943625556391327 / 600000000000000000 : ℚ),
    (1943625556391327 / 200000000000000000 : ℚ),
    (-1943625556391327 / 200000000000000000 : ℚ),
    (1943625556391327 / 600000000000000000 : ℚ)
  ],
  ![
    (1943625556391327 / 600000000000000000 : ℚ),
    (-1943625556391327 / 200000000000000000 : ℚ),
    (1943625556391327 / 200000000000000000 : ℚ),
    (-1943625556391327 / 600000000000000000 : ℚ)
  ],
  ![
    (-1943625556391327 / 1800000000000000000 : ℚ),
    (1943625556391327 / 600000000000000000 : ℚ),
    (-1943625556391327 / 600000000000000000 : ℚ),
    (1943625556391327 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_25_1_correct (a b : Fin 4) :
    correctionCellCoefficient 25 1 a b = cellMatrix_25_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 25 1 a.val b.val = cellMatrix_25_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (25, 2). -/
def cellMatrix_25_2 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_25_2_correct (a b : Fin 4) :
    correctionCellCoefficient 25 2 a b = cellMatrix_25_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 25 2 a.val b.val = cellMatrix_25_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (26, 0). -/
def cellMatrix_26_0 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_26_0_correct (a b : Fin 4) :
    correctionCellCoefficient 26 0 a b = cellMatrix_26_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 26 0 a.val b.val = cellMatrix_26_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (26, 1). -/
def cellMatrix_26_1 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_26_1_correct (a b : Fin 4) :
    correctionCellCoefficient 26 1 a b = cellMatrix_26_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 26 1 a.val b.val = cellMatrix_26_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (27, 0). -/
def cellMatrix_27_0 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_27_0_correct (a b : Fin 4) :
    correctionCellCoefficient 27 0 a b = cellMatrix_27_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 27 0 a.val b.val = cellMatrix_27_0 a b) a b

end PartialBalayage.Maximal.Square
