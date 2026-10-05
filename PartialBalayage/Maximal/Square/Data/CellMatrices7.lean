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

/-- Candidate finite rational coefficient matrix on cell (8, 6). -/
def cellMatrix_8_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (14632171518834799 / 200000000000000000 : ℚ),
    (26768948299177201 / 600000000000000000 : ℚ),
    (-2326888284051849 / 200000000000000000 : ℚ),
    (14014454035273 / 28125000000000000 : ℚ)
  ],
  ![
    (25366383766268153 / 600000000000000000 : ℚ),
    (-901539428338341 / 40000000000000000 : ℚ),
    (660311053172867 / 200000000000000000 : ℚ),
    (-115265819899447 / 150000000000000000 : ℚ)
  ],
  ![
    (-98858456527167 / 8000000000000000 : ℚ),
    (750701995303261 / 200000000000000000 : ℚ),
    (-58116342083103 / 40000000000000000 : ℚ),
    (147745863819071 / 300000000000000000 : ℚ)
  ],
  ![
    (20039553344959 / 14400000000000000 : ℚ),
    (-12321147781579 / 24000000000000000 : ℚ),
    (142733765939399 / 600000000000000000 : ℚ),
    (-72627575341331 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_6_correct (a b : Fin 4) :
    correctionCellCoefficient 8 6 a b = cellMatrix_8_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 6 a.val b.val = cellMatrix_8_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (8, 7). -/
def cellMatrix_8_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (307122110510137 / 2880000000000000 : ℚ),
    (13704543653123579 / 600000000000000000 : ℚ),
    (-243349591755923 / 24000000000000000 : ℚ),
    (365705318765189 / 600000000000000000 : ℚ)
  ],
  ![
    (13363162221113851 / 600000000000000000 : ℚ),
    (-3648138314943759 / 200000000000000000 : ℚ),
    (199247773575079 / 200000000000000000 : ℚ),
    (-25487371692321 / 40000000000000000 : ℚ)
  ],
  ![
    (-1147706331447229 / 120000000000000000 : ℚ),
    (465030302110373 / 200000000000000000 : ℚ),
    (4910017222627 / 200000000000000000 : ℚ),
    (-219304379455121 / 200000000000000000 : ℚ)
  ],
  ![
    (25717523525203 / 28125000000000000 : ℚ),
    (-96424759841833 / 150000000000000000 : ℚ),
    (-27550513845907 / 75000000000000000 : ℚ),
    (18033412670951 / 60000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_7_correct (a b : Fin 4) :
    correctionCellCoefficient 8 7 a b = cellMatrix_8_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 7 a.val b.val = cellMatrix_8_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (8, 8). -/
def cellMatrix_8_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (26988855825350963 / 225000000000000000 : ℚ),
    (658545005405749 / 150000000000000000 : ℚ),
    (-1246655959400627 / 150000000000000000 : ℚ),
    (184307217668879 / 900000000000000000 : ℚ)
  ],
  ![
    (658545005405749 / 150000000000000000 : ℚ),
    (-226997083948651 / 12500000000000000 : ℚ),
    (-22882850226217 / 25000000000000000 : ℚ),
    (-142752440386657 / 300000000000000000 : ℚ)
  ],
  ![
    (-1246655959400627 / 150000000000000000 : ℚ),
    (-22882850226217 / 25000000000000000 : ℚ),
    (-40812695071421 / 12500000000000000 : ℚ),
    (160299134680637 / 300000000000000000 : ℚ)
  ],
  ![
    (184307217668879 / 900000000000000000 : ℚ),
    (-142752440386657 / 300000000000000000 : ℚ),
    (160299134680637 / 300000000000000000 : ℚ),
    (-2873343183577799 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_8_correct (a b : Fin 4) :
    correctionCellCoefficient 8 8 a b = cellMatrix_8_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 8 a.val b.val = cellMatrix_8_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 0). -/
def cellMatrix_9_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-36650695654305121 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-635075427202601 / 37500000000000000 : ℚ),
    (8218774187769253 / 900000000000000000 : ℚ)
  ],
  ![
    (20356294811968603 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (468078828272507 / 50000000000000000 : ℚ),
    (-615268076785613 / 150000000000000000 : ℚ)
  ],
  ![
    (-4141362406221139 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-120481360461353 / 50000000000000000 : ℚ),
    (282431686574623 / 300000000000000000 : ℚ)
  ],
  ![
    (45246463983979 / 25000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (28792090111119 / 100000000000000000 : ℚ),
    (-158671603203763 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_0_correct (a b : Fin 4) :
    correctionCellCoefficient 9 0 a b = cellMatrix_9_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 0 a.val b.val = cellMatrix_9_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 1). -/
def cellMatrix_9_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-3639477643283191 / 75000000000000000 : ℚ),
    (-1942432647472363 / 300000000000000000 : ℚ),
    (209211384676563 / 20000000000000000 : ℚ),
    (36681929296147 / 300000000000000000 : ℚ)
  ],
  ![
    (7311410542677473 / 100000000000000000 : ℚ),
    (320889579759401 / 50000000000000000 : ℚ),
    (-73594624256553 / 25000000000000000 : ℚ),
    (-2395634149461 / 6250000000000000 : ℚ)
  ],
  ![
    (-763636480402439 / 50000000000000000 : ℚ),
    (-199493755270789 / 100000000000000000 : ℚ),
    (41468965651917 / 100000000000000000 : ℚ),
    (16549697394259 / 100000000000000000 : ℚ)
  ],
  ![
    (3617331425642867 / 1800000000000000000 : ℚ),
    (37366695625933 / 120000000000000000 : ℚ),
    (14080937462951 / 600000000000000000 : ℚ),
    (-36602859829991 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_1_correct (a b : Fin 4) :
    correctionCellCoefficient 9 1 a b = cellMatrix_9_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 1 a.val b.val = cellMatrix_9_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 2). -/
def cellMatrix_9_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-2665098104232107 / 60000000000000000 : ℚ),
    (555494335089121 / 37500000000000000 : ℚ),
    (541369426339481 / 50000000000000000 : ℚ),
    (-239855953006981 / 600000000000000000 : ℚ)
  ],
  ![
    (7620481058778687 / 100000000000000000 : ℚ),
    (-247873094831 / 400000000000000 : ℚ),
    (-20468446810017 / 5000000000000000 : ℚ),
    (-105298695486667 / 600000000000000000 : ℚ)
  ],
  ![
    (-1668748053029491 / 100000000000000000 : ℚ),
    (-33453365892089 / 50000000000000000 : ℚ),
    (45559028917347 / 50000000000000000 : ℚ),
    (25556345379 / 40000000000000000 : ℚ)
  ],
  ![
    (2055133046465371 / 900000000000000000 : ℚ),
    (17531128927599 / 100000000000000000 : ℚ),
    (-47863821013511 / 300000000000000000 : ℚ),
    (14684638126981 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_2_correct (a b : Fin 4) :
    correctionCellCoefficient 9 2 a b = cellMatrix_9_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 2 a.val b.val = cellMatrix_9_2 a b) a b

end PartialBalayage.Maximal.Square
