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

/-- Candidate finite rational coefficient matrix on cell (12, 6). -/
def cellMatrix_12_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (6286438552427143 / 45000000000000000 : ℚ),
    (-308717258639 / 234375000000000 : ℚ),
    (-1977789304844569 / 300000000000000000 : ℚ),
    (-515910934664873 / 1800000000000000000 : ℚ)
  ],
  ![
    (41376182294509 / 4687500000000000 : ℚ),
    (-63151206619213 / 25000000000000000 : ℚ),
    (25924080278813 / 20000000000000000 : ℚ),
    (57103879626981 / 200000000000000000 : ℚ)
  ],
  ![
    (-617689886102329 / 300000000000000000 : ℚ),
    (2946994459979 / 4000000000000000 : ℚ),
    (-69313040611 / 25000000000000000 : ℚ),
    (-108898542035327 / 600000000000000000 : ℚ)
  ],
  ![
    (-128134899518731 / 225000000000000000 : ℚ),
    (-3485279663117 / 9375000000000000 : ℚ),
    (-40912275488467 / 300000000000000000 : ℚ),
    (39886049236103 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_6_correct (a b : Fin 4) :
    correctionCellCoefficient 12 6 a b = cellMatrix_12_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 6 a.val b.val = cellMatrix_12_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 7). -/
def cellMatrix_12_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (236703946787005913 / 1800000000000000000 : ℚ),
    (-9217384336158989 / 600000000000000000 : ℚ),
    (-4471489544354011 / 600000000000000000 : ℚ),
    (-592674041708023 / 600000000000000000 : ℚ)
  ],
  ![
    (4729556422081373 / 600000000000000000 : ℚ),
    (184583591503499 / 200000000000000000 : ℚ),
    (430552441669073 / 200000000000000000 : ℚ),
    (108413754981469 / 120000000000000000 : ℚ)
  ],
  ![
    (-903892658217799 / 600000000000000000 : ℚ),
    (37342172313847 / 200000000000000000 : ℚ),
    (-21890609272043 / 40000000000000000 : ℚ),
    (-6979197880003 / 200000000000000000 : ℚ)
  ],
  ![
    (-98899019303039 / 100000000000000000 : ℚ),
    (-14197675215559 / 37500000000000000 : ℚ),
    (12953274327913 / 100000000000000000 : ℚ),
    (-385434458081849 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_7_correct (a b : Fin 4) :
    correctionCellCoefficient 12 7 a b = cellMatrix_12_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 7 a.val b.val = cellMatrix_12_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 8). -/
def cellMatrix_12_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (48464825755085711 / 450000000000000000 : ℚ),
    (-498459638749777 / 15000000000000000 : ℚ),
    (-19529723967119 / 1875000000000000 : ℚ),
    (-4654339940545309 / 1800000000000000000 : ℚ)
  ],
  ![
    (3558516648253217 / 300000000000000000 : ℚ),
    (158775724974899 / 20000000000000000 : ℚ),
    (486310608288209 / 100000000000000000 : ℚ),
    (613343610618239 / 200000000000000000 : ℚ)
  ],
  ![
    (-71322679624807 / 37500000000000000 : ℚ),
    (-1582043078489 / 1562500000000000 : ℚ),
    (-4074707500007 / 6250000000000000 : ℚ),
    (-285812949267083 / 120000000000000000 : ℚ)
  ],
  ![
    (-2613946277980949 / 1800000000000000000 : ℚ),
    (-152385989865279 / 200000000000000000 : ℚ),
    (-307714812114371 / 600000000000000000 : ℚ),
    (268082824191859 / 225000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_8_correct (a b : Fin 4) :
    correctionCellCoefficient 12 8 a b = cellMatrix_12_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 8 a.val b.val = cellMatrix_12_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 9). -/
def cellMatrix_12_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (22128254284278011 / 360000000000000000 : ℚ),
    (-37091748829492549 / 600000000000000000 : ℚ),
    (-10903851610023389 / 600000000000000000 : ℚ),
    (-944708801724029 / 200000000000000000 : ℚ)
  ],
  ![
    (133105596218699 / 4800000000000000 : ℚ),
    (5373030514756543 / 200000000000000000 : ℚ),
    (562530409686227 / 40000000000000000 : ℚ),
    (2520855006784649 / 120000000000000000 : ℚ)
  ],
  ![
    (-142756163298911 / 24000000000000000 : ℚ),
    (-378469508076491 / 40000000000000000 : ℚ),
    (-1559455386335639 / 200000000000000000 : ℚ),
    (-4372979090293611 / 200000000000000000 : ℚ)
  ],
  ![
    (-921300676525567 / 600000000000000000 : ℚ),
    (1072074999710293 / 600000000000000000 : ℚ),
    (612315927140167 / 200000000000000000 : ℚ),
    (9459236339051 / 1440000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_9_correct (a b : Fin 4) :
    correctionCellCoefficient 12 9 a b = cellMatrix_12_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 9 a.val b.val = cellMatrix_12_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 10). -/
def cellMatrix_12_10 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-2092395455633701 / 90000000000000000 : ℚ),
    (-16850457816263897 / 150000000000000000 : ℚ),
    (-388124616510793 / 12000000000000000 : ℚ),
    (50269216164804583 / 1800000000000000000 : ℚ)
  ],
  ![
    (26899761125411827 / 300000000000000000 : ℚ),
    (11801304822771029 / 100000000000000000 : ℚ),
    (770846354117719 / 10000000000000000 : ℚ),
    (-11210739032337053 / 120000000000000000 : ℚ)
  ],
  ![
    (-2704325013350789 / 60000000000000000 : ℚ),
    (-9065097791967283 / 100000000000000000 : ℚ),
    (-1834799082152059 / 25000000000000000 : ℚ),
    (14444133389142023 / 120000000000000000 : ℚ)
  ],
  ![
    (17787211737629431 / 1800000000000000000 : ℚ),
    (3314003197273009 / 120000000000000000 : ℚ),
    (13660993205234251 / 600000000000000000 : ℚ),
    (-40489477054581173 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_10_correct (a b : Fin 4) :
    correctionCellCoefficient 12 10 a b = cellMatrix_12_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 10 a.val b.val = cellMatrix_12_10 a b) a b

/-- Candidate finite rational coefficient matrix on cell (12, 11). -/
def cellMatrix_12_11 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-252002879219655151 / 1800000000000000000 : ℚ),
    (-11189015350266061 / 120000000000000000 : ℚ),
    (30862985339264933 / 600000000000000000 : ℚ),
    (13434810306225953 / 600000000000000000 : ℚ)
  ],
  ![
    (114804437272827703 / 600000000000000000 : ℚ),
    (-1617231351434447 / 200000000000000000 : ℚ),
    (-8127353615866177 / 40000000000000000 : ℚ),
    (58042885865345713 / 600000000000000000 : ℚ)
  ],
  ![
    (-53248347911250889 / 600000000000000000 : ℚ),
    (4946737209468521 / 40000000000000000 : ℚ),
    (57542274288493643 / 200000000000000000 : ℚ),
    (-40804038946105021 / 200000000000000000 : ℚ)
  ],
  ![
    (9167095067754991 / 600000000000000000 : ℚ),
    (-12362317237442933 / 200000000000000000 : ℚ),
    (-4487864060261873 / 40000000000000000 : ℚ),
    (10465243449973027 / 120000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_12_11_correct (a b : Fin 4) :
    correctionCellCoefficient 12 11 a b = cellMatrix_12_11 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 12 11 a.val b.val = cellMatrix_12_11 a b) a b

end PartialBalayage.Maximal.Square
