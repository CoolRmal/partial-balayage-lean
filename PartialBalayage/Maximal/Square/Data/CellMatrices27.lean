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

/-- Candidate finite rational coefficient matrix on cell (18, 7). -/
def cellMatrix_18_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (3842744859572351 / 200000000000000000 : ℚ),
    (-19527397800715619 / 600000000000000000 : ℚ),
    (3999581610999283 / 200000000000000000 : ℚ),
    (-2058604587284741 / 450000000000000000 : ℚ)
  ],
  ![
    (-20053169786737027 / 600000000000000000 : ℚ),
    (4995863851301487 / 200000000000000000 : ℚ),
    (2532789116416283 / 200000000000000000 : ℚ),
    (-65594954169533 / 6250000000000000 : ℚ)
  ],
  ![
    (4262467604009987 / 200000000000000000 : ℚ),
    (2269903123405579 / 200000000000000000 : ℚ),
    (-9798556091123349 / 200000000000000000 : ℚ),
    (6781441287491117 / 300000000000000000 : ℚ)
  ],
  ![
    (-2288629831169107 / 450000000000000000 : ℚ),
    (-245949442114963 / 25000000000000000 : ℚ),
    (6715719789238441 / 300000000000000000 : ℚ),
    (-1910640673592863 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_7_correct (a b : Fin 4) :
    correctionCellCoefficient 18 7 a b = cellMatrix_18_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 7 a.val b.val = cellMatrix_18_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 8). -/
def cellMatrix_18_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (752865296771777 / 360000000000000000 : ℚ),
    (-752865296771777 / 120000000000000000 : ℚ),
    (752865296771777 / 120000000000000000 : ℚ),
    (-752865296771777 / 360000000000000000 : ℚ)
  ],
  ![
    (-752865296771777 / 120000000000000000 : ℚ),
    (752865296771777 / 40000000000000000 : ℚ),
    (-752865296771777 / 40000000000000000 : ℚ),
    (752865296771777 / 120000000000000000 : ℚ)
  ],
  ![
    (752865296771777 / 120000000000000000 : ℚ),
    (-752865296771777 / 40000000000000000 : ℚ),
    (752865296771777 / 40000000000000000 : ℚ),
    (-752865296771777 / 120000000000000000 : ℚ)
  ],
  ![
    (-752865296771777 / 360000000000000000 : ℚ),
    (752865296771777 / 120000000000000000 : ℚ),
    (-752865296771777 / 120000000000000000 : ℚ),
    (752865296771777 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_8_correct (a b : Fin 4) :
    correctionCellCoefficient 18 8 a b = cellMatrix_18_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 8 a.val b.val = cellMatrix_18_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 9). -/
def cellMatrix_18_9 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_18_9_correct (a b : Fin 4) :
    correctionCellCoefficient 18 9 a b = cellMatrix_18_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 9 a.val b.val = cellMatrix_18_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 0). -/
def cellMatrix_19_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (91469241999088949 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-193076582397667 / 300000000000000000 : ℚ),
    (63472175552897 / 360000000000000000 : ℚ)
  ],
  ![
    (-1007275396337887 / 100000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-76686717474957 / 100000000000000000 : ℚ),
    (6883649786149 / 600000000000000000 : ℚ)
  ],
  ![
    (-322140108979819 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-35628953969143 / 100000000000000000 : ℚ),
    (103462291664647 / 600000000000000000 : ℚ)
  ],
  ![
    (-15555385383 / 390625000000000 : ℚ),
    (0 / 1 : ℚ),
    (29549627897323 / 100000000000000000 : ℚ),
    (-108598203824509 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_0_correct (a b : Fin 4) :
    correctionCellCoefficient 19 0 a b = cellMatrix_19_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 0 a.val b.val = cellMatrix_19_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 1). -/
def cellMatrix_19_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (182097385381556381 / 1800000000000000000 : ℚ),
    (-151648483942061 / 200000000000000000 : ℚ),
    (-68792287030849 / 600000000000000000 : ℚ),
    (-987342734491009 / 1800000000000000000 : ℚ)
  ],
  ![
    (-1299377806618183 / 120000000000000000 : ℚ),
    (-299863220113679 / 200000000000000000 : ℚ),
    (-29297957032753 / 40000000000000000 : ℚ),
    (-134344277994491 / 600000000000000000 : ℚ)
  ],
  ![
    (-754591650109849 / 600000000000000000 : ℚ),
    (-1562140968477 / 8000000000000000 : ℚ),
    (32204383726361 / 200000000000000000 : ℚ),
    (-184039217891581 / 600000000000000000 : ℚ)
  ],
  ![
    (12910635504457 / 900000000000000000 : ℚ),
    (-997466006627 / 7500000000000000 : ℚ),
    (-128547523957049 / 300000000000000000 : ℚ),
    (201070503429839 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_1_correct (a b : Fin 4) :
    correctionCellCoefficient 19 1 a b = cellMatrix_19_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 1 a.val b.val = cellMatrix_19_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (19, 2). -/
def cellMatrix_19_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (44884707357623569 / 450000000000000000 : ℚ),
    (-52662425345963 / 20000000000000000 : ℚ),
    (-528067510760929 / 300000000000000000 : ℚ),
    (-908131039113509 / 1800000000000000000 : ℚ)
  ],
  ![
    (-3985146163458869 / 300000000000000000 : ℚ),
    (-7271870684357 / 2000000000000000 : ℚ),
    (-17552128947391 / 12500000000000000 : ℚ),
    (80382032269487 / 200000000000000000 : ℚ)
  ],
  ![
    (-479589144729061 / 300000000000000000 : ℚ),
    (-4958874207837 / 6250000000000000 : ℚ),
    (-7591741708261 / 10000000000000000 : ℚ),
    (492032854175581 / 600000000000000000 : ℚ)
  ],
  ![
    (-22571712575563 / 225000000000000000 : ℚ),
    (210294637361 / 600000000000000 : ℚ),
    (273593482902629 / 300000000000000000 : ℚ),
    (-291162774176081 / 180000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_19_2_correct (a b : Fin 4) :
    correctionCellCoefficient 19 2 a b = cellMatrix_19_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 19 2 a.val b.val = cellMatrix_19_2 a b) a b

end PartialBalayage.Maximal.Square
