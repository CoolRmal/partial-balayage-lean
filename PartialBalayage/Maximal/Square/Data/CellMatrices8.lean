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

/-- Candidate finite rational coefficient matrix on cell (9, 3). -/
def cellMatrix_9_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-11506494517828343 / 600000000000000000 : ℚ),
    (21161207734552537 / 600000000000000000 : ℚ),
    (1925621752350943 / 200000000000000000 : ℚ),
    (-520210059914411 / 225000000000000000 : ℚ)
  ],
  ![
    (8557912879547383 / 120000000000000000 : ℚ),
    (-1866710987703527 / 200000000000000000 : ℚ),
    (-924036567887347 / 200000000000000000 : ℚ),
    (83516315166437 / 150000000000000000 : ℚ)
  ],
  ![
    (-657789134446211 / 40000000000000000 : ℚ),
    (46208422590221 / 40000000000000000 : ℚ),
    (182619460850073 / 200000000000000000 : ℚ),
    (-5115466085459 / 300000000000000000 : ℚ)
  ],
  ![
    (4212066678181363 / 1800000000000000000 : ℚ),
    (-856354656903 / 40000000000000000 : ℚ),
    (-22304451392117 / 600000000000000000 : ℚ),
    (-556136218061 / 14400000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_3_correct (a b : Fin 4) :
    correctionCellCoefficient 9 3 a b = cellMatrix_9_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 3 a.val b.val = cellMatrix_9_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 4). -/
def cellMatrix_9_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (42133054942015781 / 1800000000000000000 : ℚ),
    (9517752589780969 / 200000000000000000 : ℚ),
    (1615184777737541 / 600000000000000000 : ℚ),
    (-3120033719784761 / 900000000000000000 : ℚ)
  ],
  ![
    (34751386991630041 / 600000000000000000 : ℚ),
    (-3380718862812473 / 200000000000000000 : ℚ),
    (-589971307221599 / 200000000000000000 : ℚ),
    (100901846285711 / 75000000000000000 : ℚ)
  ],
  ![
    (-8636083227460549 / 600000000000000000 : ℚ),
    (586050102480333 / 200000000000000000 : ℚ),
    (34477705735831 / 40000000000000000 : ℚ),
    (-64086805409737 / 150000000000000000 : ℚ)
  ],
  ![
    (21026564256181 / 9375000000000000 : ℚ),
    (-31742812473851 / 150000000000000000 : ℚ),
    (-15303579774957 / 100000000000000000 : ℚ),
    (164320408907851 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_4_correct (a b : Fin 4) :
    correctionCellCoefficient 9 4 a b = cellMatrix_9_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 4 a.val b.val = cellMatrix_9_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 5). -/
def cellMatrix_9_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (126398315143687603 / 1800000000000000000 : ℚ),
    (8514519961749489 / 200000000000000000 : ℚ),
    (-4624882661831981 / 600000000000000000 : ℚ),
    (-1103860396112111 / 1800000000000000000 : ℚ)
  ],
  ![
    (23646531251813513 / 600000000000000000 : ℚ),
    (-3753446706969983 / 200000000000000000 : ℚ),
    (217243463064089 / 200000000000000000 : ℚ),
    (4637935217147 / 600000000000000000 : ℚ)
  ],
  ![
    (-6617114555621033 / 600000000000000000 : ℚ),
    (134895987639939 / 40000000000000000 : ℚ),
    (-83958692959793 / 200000000000000000 : ℚ),
    (-63889251516323 / 600000000000000000 : ℚ)
  ],
  ![
    (709008512091833 / 360000000000000000 : ℚ),
    (-146293798287037 / 600000000000000000 : ℚ),
    (72498930258109 / 600000000000000000 : ℚ),
    (15821823134111 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_5_correct (a b : Fin 4) :
    correctionCellCoefficient 9 5 a b = cellMatrix_9_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 5 a.val b.val = cellMatrix_9_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 6). -/
def cellMatrix_9_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (3761009728356499 / 36000000000000000 : ℚ),
    (2531655694245399 / 100000000000000000 : ℚ),
    (-1432185764486023 / 150000000000000000 : ℚ),
    (12357508557293 / 600000000000000000 : ℚ)
  ],
  ![
    (6521279727656489 / 300000000000000000 : ℚ),
    (-1657160922812329 / 100000000000000000 : ℚ),
    (55470349570309 / 50000000000000000 : ℚ),
    (-77739233676053 / 200000000000000000 : ℚ)
  ],
  ![
    (-98188801428353 / 12000000000000000 : ℚ),
    (221336650381893 / 100000000000000000 : ℚ),
    (-36961986119029 / 50000000000000000 : ℚ),
    (-22548716356171 / 200000000000000000 : ℚ)
  ],
  ![
    (173302718228969 / 90000000000000000 : ℚ),
    (7055023521809 / 30000000000000000 : ℚ),
    (53723834616277 / 150000000000000000 : ℚ),
    (143116397478727 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_6_correct (a b : Fin 4) :
    correctionCellCoefficient 9 6 a b = cellMatrix_9_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 6 a.val b.val = cellMatrix_9_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 7). -/
def cellMatrix_9_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (43294226453216347 / 360000000000000000 : ℚ),
    (3769520575256089 / 600000000000000000 : ℚ),
    (-5691670532272213 / 600000000000000000 : ℚ),
    (-494184268275479 / 600000000000000000 : ℚ)
  ],
  ![
    (3532020412254553 / 600000000000000000 : ℚ),
    (-620755350018069 / 40000000000000000 : ℚ),
    (-11336302746923 / 200000000000000000 : ℚ),
    (-385711490662337 / 200000000000000000 : ℚ)
  ],
  ![
    (-4092610151623153 / 600000000000000000 : ℚ),
    (79331262743041 / 200000000000000000 : ℚ),
    (-215494093544629 / 200000000000000000 : ℚ),
    (-38970252745611 / 200000000000000000 : ℚ)
  ],
  ![
    (4677158188761971 / 1800000000000000000 : ℚ),
    (714007544845123 / 600000000000000000 : ℚ),
    (71602347188767 / 120000000000000000 : ℚ),
    (87017699169827 / 150000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_7_correct (a b : Fin 4) :
    correctionCellCoefficient 9 7 a b = cellMatrix_9_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 7 a.val b.val = cellMatrix_9_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (9, 8). -/
def cellMatrix_9_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (104611064795103463 / 900000000000000000 : ℚ),
    (-4548186647057387 / 300000000000000000 : ℚ),
    (-143484466741973 / 12000000000000000 : ℚ),
    (-43939931383783 / 15000000000000000 : ℚ)
  ],
  ![
    (-3485226609122131 / 300000000000000000 : ℚ),
    (-2141791913785601 / 100000000000000000 : ℚ),
    (-584235387366967 / 100000000000000000 : ℚ),
    (-1347748677301591 / 150000000000000000 : ℚ)
  ],
  ![
    (-18472037609059 / 2400000000000000 : ℚ),
    (-9371353651661 / 4000000000000000 : ℚ),
    (-166202425890731 / 100000000000000000 : ℚ),
    (-452174008149527 / 50000000000000000 : ℚ)
  ],
  ![
    (8937428421166769 / 1800000000000000000 : ℚ),
    (2474243406770717 / 600000000000000000 : ℚ),
    (1402224125981759 / 600000000000000000 : ℚ),
    (4681842620458301 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_9_8_correct (a b : Fin 4) :
    correctionCellCoefficient 9 8 a b = cellMatrix_9_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 9 8 a.val b.val = cellMatrix_9_8 a b) a b

end PartialBalayage.Maximal.Square
