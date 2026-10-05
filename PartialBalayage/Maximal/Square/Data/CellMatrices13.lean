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

/-- Candidate finite rational coefficient matrix on cell (12, 0). -/
def cellMatrix_12_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (3060782672972531 / 37500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-8906877928733 / 3125000000000000 : ℚ),
    (2354173083769 / 900000000000000 : ℚ)
  ],
  ![
    (590565286393577 / 25000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (5220605918391 / 2500000000000000 : ℚ),
    (-106012386748657 / 100000000000000000 : ℚ)
  ],
  ![
    (-41551847859309 / 10000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-5722839756753 / 10000000000000000 : ℚ),
    (39501611136137 / 150000000000000000 : ℚ)
  ],
  ![
    (48443237909407 / 450000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (27410210957021 / 300000000000000000 : ℚ),
    (-87784858638103 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_0_correct (a b : Fin 4) :
    correctionCellCoefficient 12 0 a b = cellMatrix_12_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 0 a.val b.val = cellMatrix_12_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 1). -/
def cellMatrix_12_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (915597204895433 / 11250000000000000 : ℚ),
    (80506565181533 / 37500000000000000 : ℚ),
    (187389100326329 / 37500000000000000 : ℚ),
    (-251005616081803 / 600000000000000000 : ℚ)
  ],
  ![
    (2465072995561291 / 100000000000000000 : ℚ),
    (99611313225309 / 100000000000000000 : ℚ),
    (-109212923510331 / 100000000000000000 : ℚ),
    (-6143319240497 / 200000000000000000 : ℚ)
  ],
  ![
    (-669618703104793 / 150000000000000000 : ℚ),
    (-17726786431393 / 50000000000000000 : ℚ),
    (2721853088093 / 12500000000000000 : ℚ),
    (-4773028025077 / 200000000000000000 : ℚ)
  ],
  ![
    (90149786247217 / 600000000000000000 : ℚ),
    (21855985189981 / 600000000000000000 : ℚ),
    (-10988145574687 / 200000000000000000 : ℚ),
    (735634486093 / 45000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_1_correct (a b : Fin 4) :
    correctionCellCoefficient 12 1 a b = cellMatrix_12_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 1 a.val b.val = cellMatrix_12_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 2). -/
def cellMatrix_12_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (158601527879401247 / 1800000000000000000 : ℚ),
    (2177179801700549 / 200000000000000000 : ℚ),
    (449041751395171 / 120000000000000000 : ℚ),
    (-160304614248539 / 300000000000000000 : ℚ)
  ],
  ![
    (4904799451312041 / 200000000000000000 : ℚ),
    (-256059025312197 / 200000000000000000 : ℚ),
    (-236855804742153 / 200000000000000000 : ℚ),
    (648650088523 / 100000000000000000 : ℚ)
  ],
  ![
    (-554973277088531 / 120000000000000000 : ℚ),
    (1873069018173 / 200000000000000000 : ℚ),
    (29230565334257 / 200000000000000000 : ℚ),
    (5574941328389 / 100000000000000000 : ℚ)
  ],
  ![
    (266549383583131 / 1800000000000000000 : ℚ),
    (-14647508814421 / 600000000000000000 : ℚ),
    (-3539057280341 / 600000000000000000 : ℚ),
    (-42717778140679 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_2_correct (a b : Fin 4) :
    correctionCellCoefficient 12 2 a b = cellMatrix_12_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 2 a.val b.val = cellMatrix_12_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 3). -/
def cellMatrix_12_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (183969944680142519 / 1800000000000000000 : ℚ),
    (10060129233562123 / 600000000000000000 : ℚ),
    (1283381071484621 / 600000000000000000 : ℚ),
    (-1044214870315927 / 900000000000000000 : ℚ)
  ],
  ![
    (4413181921434737 / 200000000000000000 : ℚ),
    (-145175746853073 / 40000000000000000 : ℚ),
    (-46592780842203 / 40000000000000000 : ℚ),
    (84049290478639 / 300000000000000000 : ℚ)
  ],
  ![
    (-2648105834415031 / 600000000000000000 : ℚ),
    (93783847657021 / 200000000000000000 : ℚ),
    (62680213304591 / 200000000000000000 : ℚ),
    (-1177573115537 / 15000000000000000 : ℚ)
  ],
  ![
    (28211984526361 / 300000000000000000 : ℚ),
    (-10740566919297 / 100000000000000000 : ℚ),
    (-770947257017 / 10000000000000000 : ℚ),
    (34443181463749 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_3_correct (a b : Fin 4) :
    correctionCellCoefficient 12 3 a b = cellMatrix_12_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 3 a.val b.val = cellMatrix_12_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 4). -/
def cellMatrix_12_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (23990227317183433 / 200000000000000000 : ℚ),
    (3512820545299837 / 200000000000000000 : ℚ),
    (-268349556382411 / 200000000000000000 : ℚ),
    (-826342200147419 / 600000000000000000 : ℚ)
  ],
  ![
    (10531116429832349 / 600000000000000000 : ℚ),
    (-1023707961730117 / 200000000000000000 : ℚ),
    (-64865323253737 / 200000000000000000 : ℚ),
    (75642245958249 / 200000000000000000 : ℚ)
  ],
  ![
    (-29677554348689 / 8000000000000000 : ℚ),
    (172041349644723 / 200000000000000000 : ℚ),
    (15577288683111 / 200000000000000000 : ℚ),
    (-11811498061703 / 200000000000000000 : ℚ)
  ],
  ![
    (-128385622188491 / 1800000000000000000 : ℚ),
    (-122513890894073 / 600000000000000000 : ℚ),
    (-11813653957271 / 600000000000000000 : ℚ),
    (4180376325833 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_4_correct (a b : Fin 4) :
    correctionCellCoefficient 12 4 a b = cellMatrix_12_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 4 a.val b.val = cellMatrix_12_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 5). -/
def cellMatrix_12_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (40438876359077579 / 300000000000000000 : ℚ),
    (537444808096899 / 50000000000000000 : ℚ),
    (-109469175652983 / 20000000000000000 : ℚ),
    (-10492239689057 / 28125000000000000 : ℚ)
  ],
  ![
    (3746161656377767 / 300000000000000000 : ℚ),
    (-231627967590711 / 50000000000000000 : ℚ),
    (16206141462101 / 20000000000000000 : ℚ),
    (404914117363 / 2500000000000000 : ℚ)
  ],
  ![
    (-283065859225547 / 100000000000000000 : ℚ),
    (41940358206459 / 50000000000000000 : ℚ),
    (-9928602750999 / 100000000000000000 : ℚ),
    (1930270117711 / 60000000000000000 : ℚ)
  ],
  ![
    (-523007504090857 / 1800000000000000000 : ℚ),
    (-137780446156949 / 600000000000000000 : ℚ),
    (-690580261121 / 120000000000000000 : ℚ),
    (-78371649671329 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_5_correct (a b : Fin 4) :
    correctionCellCoefficient 12 5 a b = cellMatrix_12_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 5 a.val b.val = cellMatrix_12_5 a b) a b

end PartialBalayage.Maximal.Square
