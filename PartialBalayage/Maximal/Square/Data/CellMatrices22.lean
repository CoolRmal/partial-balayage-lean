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

/-- Candidate finite rational coefficient matrix on cell (16, 0). -/
def cellMatrix_16_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (107955423306394351 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (39889871958337 / 300000000000000000 : ℚ),
    (1184529716437531 / 1800000000000000000 : ℚ)
  ],
  ![
    (-382688945037997 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (4936317152357 / 100000000000000000 : ℚ),
    (-141345698566541 / 600000000000000000 : ℚ)
  ],
  ![
    (-121555824877051 / 60000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (16318687195549 / 100000000000000000 : ℚ),
    (-73309467143693 / 600000000000000000 : ℚ)
  ],
  ![
    (30557369341391 / 180000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-472146119891 / 3000000000000000 : ℚ),
    (10817590280863 / 120000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_0_correct (a b : Fin 4) :
    correctionCellCoefficient 16 0 a b = cellMatrix_16_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 0 a.val b.val = cellMatrix_16_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 1). -/
def cellMatrix_16_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (14488981037398417 / 120000000000000000 : ℚ),
    (1344089204270879 / 600000000000000000 : ℚ),
    (84287297356947 / 40000000000000000 : ℚ),
    (-190967068527373 / 360000000000000000 : ℚ)
  ],
  ![
    (-877105685728393 / 600000000000000000 : ℚ),
    (-121600429957113 / 200000000000000000 : ℚ),
    (-131473064261827 / 200000000000000000 : ℚ),
    (2211574565343 / 200000000000000000 : ℚ)
  ],
  ![
    (-396985197580303 / 200000000000000000 : ℚ),
    (-8034718361497 / 200000000000000000 : ℚ),
    (-8134418550519 / 40000000000000000 : ℚ),
    (56841648866527 / 600000000000000000 : ℚ)
  ],
  ![
    (36909975138451 / 360000000000000000 : ℚ),
    (-5318918748691 / 120000000000000000 : ℚ),
    (13566926046949 / 120000000000000000 : ℚ),
    (-55218289446817 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_1_correct (a b : Fin 4) :
    correctionCellCoefficient 16 1 a b = cellMatrix_16_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 1 a.val b.val = cellMatrix_16_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 2). -/
def cellMatrix_16_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (112102538106107321 / 900000000000000000 : ℚ),
    (121578032597601 / 25000000000000000 : ℚ),
    (15473705885867 / 30000000000000000 : ℚ),
    (-19635223115979 / 50000000000000000 : ℚ)
  ],
  ![
    (-50927857646537 / 18750000000000000 : ℚ),
    (-188955917392369 / 100000000000000000 : ℚ),
    (-62419170282899 / 100000000000000000 : ℚ),
    (-7700339957 / 10000000000000000 : ℚ)
  ],
  ![
    (-640117188608329 / 300000000000000000 : ℚ),
    (-203357843751 / 1250000000000000 : ℚ),
    (4042389028483 / 50000000000000000 : ℚ),
    (-5807648296759 / 100000000000000000 : ℚ)
  ],
  ![
    (65944468757497 / 600000000000000000 : ℚ),
    (-453970722533 / 200000000000000000 : ℚ),
    (-14200649552963 / 200000000000000000 : ℚ),
    (9280027519961 / 225000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_2_correct (a b : Fin 4) :
    correctionCellCoefficient 16 2 a b = cellMatrix_16_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 2 a.val b.val = cellMatrix_16_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 3). -/
def cellMatrix_16_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (23318024888021869 / 180000000000000000 : ℚ),
    (141497649280093 / 30000000000000000 : ℚ),
    (-24837119653619 / 37500000000000000 : ℚ),
    (-56152840232551 / 90000000000000000 : ℚ)
  ],
  ![
    (-784600997784553 / 150000000000000000 : ℚ),
    (-314025268156877 / 100000000000000000 : ℚ),
    (-62650180481609 / 100000000000000000 : ℚ),
    (9303652542227 / 150000000000000000 : ℚ)
  ],
  ![
    (-170522920456987 / 75000000000000000 : ℚ),
    (-700880651057 / 4000000000000000 : ℚ),
    (-9338166833311 / 100000000000000000 : ℚ),
    (1524063461107 / 37500000000000000 : ℚ)
  ],
  ![
    (28036408790543 / 360000000000000000 : ℚ),
    (-12325589325689 / 600000000000000000 : ℚ),
    (31638271500799 / 600000000000000000 : ℚ),
    (-188138723181119 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_3_correct (a b : Fin 4) :
    correctionCellCoefficient 16 3 a b = cellMatrix_16_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 3 a.val b.val = cellMatrix_16_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 4). -/
def cellMatrix_16_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (119677434644499769 / 900000000000000000 : ℚ),
    (114013544004379 / 75000000000000000 : ℚ),
    (-380112679777231 / 150000000000000000 : ℚ),
    (-8332371683853 / 12500000000000000 : ℚ)
  ],
  ![
    (-268062103640011 / 30000000000000000 : ℚ),
    (-420718324035641 / 100000000000000000 : ℚ),
    (-8808575079431 / 20000000000000000 : ℚ),
    (-9715039336793 / 75000000000000000 : ℚ)
  ],
  ![
    (-7504797234683 / 3000000000000000 : ℚ),
    (-24005842254191 / 100000000000000000 : ℚ),
    (570868171109 / 20000000000000000 : ℚ),
    (-5734567429403 / 20000000000000000 : ℚ)
  ],
  ![
    (4990683648463 / 900000000000000000 : ℚ),
    (-13718776950521 / 60000000000000000 : ℚ),
    (-489063911501 / 1875000000000000 : ℚ),
    (736169312880331 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_4_correct (a b : Fin 4) :
    correctionCellCoefficient 16 4 a b = cellMatrix_16_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 4 a.val b.val = cellMatrix_16_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (16, 5). -/
def cellMatrix_16_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (23632998066530303 / 180000000000000000 : ℚ),
    (-69346971013701 / 12500000000000000 : ℚ),
    (-680078060395939 / 150000000000000000 : ℚ),
    (-77268709468337 / 300000000000000000 : ℚ)
  ],
  ![
    (-137125493068189 / 10000000000000000 : ℚ),
    (-547664232177123 / 100000000000000000 : ℚ),
    (-82903032744327 / 100000000000000000 : ℚ),
    (63377156451937 / 150000000000000000 : ℚ)
  ],
  ![
    (-899952739105283 / 300000000000000000 : ℚ),
    (-52157835992073 / 50000000000000000 : ℚ),
    (-166328341171 / 200000000000000 : ℚ),
    (96282850012269 / 100000000000000000 : ℚ)
  ],
  ![
    (-44971327793111 / 600000000000000000 : ℚ),
    (95326880004827 / 200000000000000000 : ℚ),
    (193222953733337 / 200000000000000000 : ℚ),
    (-1739120376958231 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_16_5_correct (a b : Fin 4) :
    correctionCellCoefficient 16 5 a b = cellMatrix_16_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 16 5 a.val b.val = cellMatrix_16_5 a b) a b

end PartialBalayage.Maximal.Square
