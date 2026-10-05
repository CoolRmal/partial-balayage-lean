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

/-- Candidate finite rational coefficient matrix on cell (13, 11). -/
def cellMatrix_13_11 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-4979165741457467 / 225000000000000000 : ℚ),
    (-2368266437593463 / 60000000000000000 : ℚ),
    (1782692882853139 / 75000000000000000 : ℚ),
    (695898291560869 / 300000000000000000 : ℚ)
  ],
  ![
    (17904513326795449 / 300000000000000000 : ℚ),
    (2690797257730491 / 50000000000000000 : ℚ),
    (3564909796864153 / 100000000000000000 : ℚ),
    (-1862668503855563 / 37500000000000000 : ℚ)
  ],
  ![
    (-6436765676996479 / 150000000000000000 : ℚ),
    (-6176632832493097 / 100000000000000000 : ℚ),
    (-2443921653858613 / 50000000000000000 : ℚ),
    (5761089151880057 / 100000000000000000 : ℚ)
  ],
  ![
    (46960440884531 / 4687500000000000 : ℚ),
    (1583157541754183 / 60000000000000000 : ℚ),
    (701279057563667 / 50000000000000000 : ℚ),
    (-475905318063229 / 25000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_11_correct (a b : Fin 4) :
    correctionCellCoefficient 13 11 a b = cellMatrix_13_11 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 11 a.val b.val = cellMatrix_13_11 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 12). -/
def cellMatrix_13_12 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-15980325030405769 / 450000000000000000 : ℚ),
    (1126976437385101 / 75000000000000000 : ℚ),
    (9218466406095163 / 300000000000000000 : ℚ),
    (-32163304967825893 / 1800000000000000000 : ℚ)
  ],
  ![
    (198951188219509 / 2000000000000000 : ℚ),
    (-149370870103451 / 6250000000000000 : ℚ),
    (-11336438233980351 / 100000000000000000 : ℚ),
    (36399248623596269 / 600000000000000000 : ℚ)
  ],
  ![
    (-7195923079745939 / 75000000000000000 : ℚ),
    (665474003856311 / 50000000000000000 : ℚ),
    (2479084829584589 / 20000000000000000 : ℚ),
    (-38517220451481457 / 600000000000000000 : ℚ)
  ],
  ![
    (3139355484668051 / 100000000000000000 : ℚ),
    (-32058202029653 / 12000000000000000 : ℚ),
    (-2154152850815707 / 50000000000000000 : ℚ),
    (39576206365424051 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_12_correct (a b : Fin 4) :
    correctionCellCoefficient 13 12 a b = cellMatrix_13_12 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 12 a.val b.val = cellMatrix_13_12 a b) a b

/-- Candidate finite rational coefficient matrix on cell (13, 13). -/
def cellMatrix_13_13 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-13726372155635567 / 1800000000000000000 : ℚ),
    (13726372155635567 / 600000000000000000 : ℚ),
    (-13726372155635567 / 600000000000000000 : ℚ),
    (13726372155635567 / 1800000000000000000 : ℚ)
  ],
  ![
    (13726372155635567 / 600000000000000000 : ℚ),
    (-13726372155635567 / 200000000000000000 : ℚ),
    (13726372155635567 / 200000000000000000 : ℚ),
    (-13726372155635567 / 600000000000000000 : ℚ)
  ],
  ![
    (-13726372155635567 / 600000000000000000 : ℚ),
    (13726372155635567 / 200000000000000000 : ℚ),
    (-13726372155635567 / 200000000000000000 : ℚ),
    (13726372155635567 / 600000000000000000 : ℚ)
  ],
  ![
    (13726372155635567 / 1800000000000000000 : ℚ),
    (-13726372155635567 / 600000000000000000 : ℚ),
    (13726372155635567 / 600000000000000000 : ℚ),
    (-13726372155635567 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_13_13_correct (a b : Fin 4) :
    correctionCellCoefficient 13 13 a b = cellMatrix_13_13 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 13 13 a.val b.val = cellMatrix_13_13 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 0). -/
def cellMatrix_14_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (12739765225307617 / 112500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-5770728585157 / 18750000000000000 : ℚ),
    (433037730133069 / 360000000000000000 : ℚ)
  ],
  ![
    (217526504205373 / 25000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (16698444207453 / 25000000000000000 : ℚ),
    (-91899345405639 / 200000000000000000 : ℚ)
  ],
  ![
    (-465286015279133 / 150000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-157285556983 / 625000000000000 : ℚ),
    (61926667917587 / 600000000000000000 : ℚ)
  ],
  ![
    (20324411027879 / 90000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-669769880291 / 150000000000000000 : ℚ),
    (607827806703 / 100000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_0_correct (a b : Fin 4) :
    correctionCellCoefficient 14 0 a b = cellMatrix_14_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 0 a.val b.val = cellMatrix_14_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 1). -/
def cellMatrix_14_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (4565498718031381 / 40000000000000000 : ℚ),
    (1795862021215297 / 600000000000000000 : ℚ),
    (660175111980107 / 200000000000000000 : ℚ),
    (-94004038453899 / 200000000000000000 : ℚ)
  ],
  ![
    (1781900241896969 / 200000000000000000 : ℚ),
    (-8522928897669 / 200000000000000000 : ℚ),
    (-142110482557293 / 200000000000000000 : ℚ),
    (-4018554405259 / 600000000000000000 : ℚ)
  ],
  ![
    (-5200564074407 / 1600000000000000 : ℚ),
    (-38736088551533 / 200000000000000000 : ℚ),
    (11595289683027 / 200000000000000000 : ℚ),
    (-98806889701 / 40000000000000000 : ℚ)
  ],
  ![
    (204695941257371 / 900000000000000000 : ℚ),
    (2791370739163 / 300000000000000000 : ℚ),
    (826182099949 / 60000000000000000 : ℚ),
    (-6957010121449 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_1_correct (a b : Fin 4) :
    correctionCellCoefficient 14 1 a b = cellMatrix_14_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 1 a.val b.val = cellMatrix_14_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (14, 2). -/
def cellMatrix_14_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (17994214003066159 / 150000000000000000 : ℚ),
    (153464885844089 / 18750000000000000 : ℚ),
    (37816299661841 / 20000000000000000 : ℚ),
    (-413814477700039 / 900000000000000000 : ℚ)
  ],
  ![
    (2444890968460381 / 300000000000000000 : ℚ),
    (-148381224208757 / 100000000000000000 : ℚ),
    (-18266129620319 / 25000000000000000 : ℚ),
    (1801315623551 / 60000000000000000 : ℚ)
  ],
  ![
    (-338852671308943 / 100000000000000000 : ℚ),
    (-8513806265497 / 100000000000000000 : ℚ),
    (1264148292189 / 25000000000000000 : ℚ),
    (-99016490659 / 75000000000000000 : ℚ)
  ],
  ![
    (430054539583843 / 1800000000000000000 : ℚ),
    (1235353112959 / 600000000000000000 : ℚ),
    (-12609209364857 / 600000000000000000 : ℚ),
    (234338861543 / 45000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_14_2_correct (a b : Fin 4) :
    correctionCellCoefficient 14 2 a b = cellMatrix_14_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 14 2 a.val b.val = cellMatrix_14_2 a b) a b

end PartialBalayage.Maximal.Square
