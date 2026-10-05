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

/-- Candidate finite rational coefficient matrix on cell (22, 3). -/
def cellMatrix_22_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (8043536268809561 / 600000000000000000 : ℚ),
    (-13181051327045371 / 600000000000000000 : ℚ),
    (513751505823581 / 40000000000000000 : ℚ),
    (-4968883217507887 / 1800000000000000000 : ℚ)
  ],
  ![
    (-2863305234003211 / 120000000000000000 : ℚ),
    (3366968690632743 / 200000000000000000 : ℚ),
    (2107810049058913 / 200000000000000000 : ℚ),
    (-1615066472968247 / 200000000000000000 : ℚ)
  ],
  ![
    (3136494950603247 / 200000000000000000 : ℚ),
    (1540072627573571 / 200000000000000000 : ℚ),
    (-7014851367265227 / 200000000000000000 : ℚ),
    (1950448147422211 / 120000000000000000 : ℚ)
  ],
  ![
    (-869495524088323 / 225000000000000000 : ℚ),
    (-166399720278197 / 25000000000000000 : ℚ),
    (73971656456003 / 4687500000000000 : ℚ),
    (-339048927672617 / 50000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_22_3_correct (a b : Fin 4) :
    correctionCellCoefficient 22 3 a b = cellMatrix_22_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 22 3 a.val b.val = cellMatrix_22_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (22, 4). -/
def cellMatrix_22_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (684347342461457 / 450000000000000000 : ℚ),
    (-684347342461457 / 150000000000000000 : ℚ),
    (684347342461457 / 150000000000000000 : ℚ),
    (-684347342461457 / 450000000000000000 : ℚ)
  ],
  ![
    (-684347342461457 / 150000000000000000 : ℚ),
    (684347342461457 / 50000000000000000 : ℚ),
    (-684347342461457 / 50000000000000000 : ℚ),
    (684347342461457 / 150000000000000000 : ℚ)
  ],
  ![
    (684347342461457 / 150000000000000000 : ℚ),
    (-684347342461457 / 50000000000000000 : ℚ),
    (684347342461457 / 50000000000000000 : ℚ),
    (-684347342461457 / 150000000000000000 : ℚ)
  ],
  ![
    (-684347342461457 / 450000000000000000 : ℚ),
    (684347342461457 / 150000000000000000 : ℚ),
    (-684347342461457 / 150000000000000000 : ℚ),
    (684347342461457 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_22_4_correct (a b : Fin 4) :
    correctionCellCoefficient 22 4 a b = cellMatrix_22_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 22 4 a.val b.val = cellMatrix_22_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (22, 5). -/
def cellMatrix_22_5 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_22_5_correct (a b : Fin 4) :
    correctionCellCoefficient 22 5 a b = cellMatrix_22_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 22 5 a.val b.val = cellMatrix_22_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (23, 0). -/
def cellMatrix_23_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (877634479002433 / 20000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-379209169895277 / 50000000000000000 : ℚ),
    (-592098697059311 / 450000000000000000 : ℚ)
  ],
  ![
    (-1825772347408843 / 100000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-199961724343017 / 12500000000000000 : ℚ),
    (2618897801183759 / 300000000000000000 : ℚ)
  ],
  ![
    (43651041377671 / 100000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1146854233685973 / 50000000000000000 : ℚ),
    (1352516749761161 / 75000000000000000 : ℚ)
  ],
  ![
    (-1345022277868909 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (3092017577410657 / 150000000000000000 : ℚ),
    (-3084996933436459 / 225000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_23_0_correct (a b : Fin 4) :
    correctionCellCoefficient 23 0 a b = cellMatrix_23_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 23 0 a.val b.val = cellMatrix_23_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (23, 1). -/
def cellMatrix_23_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (31483589102875877 / 900000000000000000 : ℚ),
    (-2867353716430973 / 150000000000000000 : ℚ),
    (-864863103372571 / 75000000000000000 : ℚ),
    (4553181338076547 / 600000000000000000 : ℚ)
  ],
  ![
    (-3828750312637589 / 150000000000000000 : ℚ),
    (-580489788304513 / 100000000000000000 : ℚ),
    (1019204006439623 / 100000000000000000 : ℚ),
    (-23601571911199 / 600000000000000000 : ℚ)
  ],
  ![
    (-1340105278938181 / 300000000000000000 : ℚ),
    (51415629018797 / 6250000000000000 : ℚ),
    (1558179265836349 / 50000000000000000 : ℚ),
    (-4208415439474001 / 200000000000000000 : ℚ)
  ],
  ![
    (4867095452849197 / 900000000000000000 : ℚ),
    (1170107329033 / 12500000000000000 : ℚ),
    (-3077976289462261 / 150000000000000000 : ℚ),
    (20893295819979931 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_23_1_correct (a b : Fin 4) :
    correctionCellCoefficient 23 1 a b = cellMatrix_23_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 23 1 a.val b.val = cellMatrix_23_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (23, 2). -/
def cellMatrix_23_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (4292352628373603 / 360000000000000000 : ℚ),
    (-3882560168485129 / 200000000000000000 : ℚ),
    (6740639187249073 / 600000000000000000 : ℚ),
    (-119086625781831 / 50000000000000000 : ℚ)
  ],
  ![
    (-847087834243393 / 40000000000000000 : ℚ),
    (2892234877238267 / 200000000000000000 : ℚ),
    (2014806440968047 / 200000000000000000 : ℚ),
    (-1117081775017801 / 150000000000000000 : ℚ)
  ],
  ![
    (1665718939908467 / 120000000000000000 : ℚ),
    (1485487936870293 / 200000000000000000 : ℚ),
    (-6392529255076607 / 200000000000000000 : ℚ),
    (737170826181647 / 50000000000000000 : ℚ)
  ],
  ![
    (-409315552832537 / 120000000000000000 : ℚ),
    (-3674349343924573 / 600000000000000000 : ℚ),
    (2860463554043629 / 200000000000000000 : ℚ),
    (-2758727830308511 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_23_2_correct (a b : Fin 4) :
    correctionCellCoefficient 23 2 a b = cellMatrix_23_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 23 2 a.val b.val = cellMatrix_23_2 a b) a b

end PartialBalayage.Maximal.Square
