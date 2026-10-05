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

/-- Candidate finite rational coefficient matrix on cell (20, 0). -/
def cellMatrix_20_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (81401503497186077 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-220687356518999 / 150000000000000000 : ℚ),
    (71335295606279 / 600000000000000000 : ℚ)
  ],
  ![
    (-3701946014895731 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-29647870860637 / 50000000000000000 : ℚ),
    (-220584582182593 / 600000000000000000 : ℚ)
  ],
  ![
    (-357979716902251 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (26509964861413 / 50000000000000000 : ℚ),
    (-110310174544463 / 200000000000000000 : ℚ)
  ],
  ![
    (38973267007007 / 225000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-61655354448953 / 60000000000000000 : ℚ),
    (1384703961180463 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_0_correct (a b : Fin 4) :
    correctionCellCoefficient 20 0 a b = cellMatrix_20_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 0 a.val b.val = cellMatrix_20_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (20, 1). -/
def cellMatrix_20_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (160368764602963003 / 1800000000000000000 : ℚ),
    (-310298593066631 / 120000000000000000 : ℚ),
    (-668743539257159 / 600000000000000000 : ℚ),
    (-1138211208429869 / 1800000000000000000 : ℚ)
  ],
  ![
    (-7980251062301699 / 600000000000000000 : ℚ),
    (-457767549067689 / 200000000000000000 : ℚ),
    (-339176065625141 / 200000000000000000 : ℚ),
    (301859299941703 / 600000000000000000 : ℚ)
  ],
  ![
    (-145754075820187 / 120000000000000000 : ℚ),
    (-23770160948417 / 40000000000000000 : ℚ),
    (-224890664187737 / 200000000000000000 : ℚ),
    (24809711833111 / 24000000000000000 : ℚ)
  ],
  ![
    (-153170536232071 / 1800000000000000000 : ℚ),
    (50532290733801 / 200000000000000000 : ℚ),
    (768150416690933 / 600000000000000000 : ℚ),
    (-3169293208701107 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_1_correct (a b : Fin 4) :
    correctionCellCoefficient 20 1 a b = cellMatrix_20_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 1 a.val b.val = cellMatrix_20_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (20, 2). -/
def cellMatrix_20_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (9535615242547637 / 112500000000000000 : ℚ),
    (-2013595626138671 / 300000000000000000 : ℚ),
    (-451738686921757 / 150000000000000000 : ℚ),
    (-1620221927922193 / 1800000000000000000 : ℚ)
  ],
  ![
    (-5034611303219243 / 300000000000000000 : ℚ),
    (-208565095094067 / 50000000000000000 : ℚ),
    (-18658382841719 / 100000000000000000 : ℚ),
    (-562138645533729 / 200000000000000000 : ℚ)
  ],
  ![
    (-569875995031313 / 300000000000000000 : ℚ),
    (6451332838777 / 25000000000000000 : ℚ),
    (197676065820019 / 100000000000000000 : ℚ),
    (-2419594887585229 / 600000000000000000 : ℚ)
  ],
  ![
    (-6258020869513 / 20000000000000000 : ℚ),
    (-740697751558919 / 300000000000000000 : ℚ),
    (-400190465335029 / 100000000000000000 : ℚ),
    (10860703985232343 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_2_correct (a b : Fin 4) :
    correctionCellCoefficient 20 2 a b = cellMatrix_20_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 2 a.val b.val = cellMatrix_20_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (20, 3). -/
def cellMatrix_20_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (133447183952946889 / 1800000000000000000 : ℚ),
    (-9261322675573591 / 600000000000000000 : ℚ),
    (-3427176675609221 / 600000000000000000 : ℚ),
    (-36875830144293 / 20000000000000000 : ℚ)
  ],
  ![
    (-14370369981218791 / 600000000000000000 : ℚ),
    (-2595309848344331 / 200000000000000000 : ℚ),
    (-13789861618277 / 1600000000000000 : ℚ),
    (79544257240361 / 10000000000000000 : ℚ)
  ],
  ![
    (-2218458494597093 / 600000000000000000 : ℚ),
    (-1577279961594937 / 200000000000000000 : ℚ),
    (-2024242755945191 / 200000000000000000 : ℚ),
    (1506004576929153 / 100000000000000000 : ℚ)
  ],
  ![
    (-1350132778407863 / 1800000000000000000 : ℚ),
    (1525674299364719 / 200000000000000000 : ℚ),
    (8459561193222169 / 600000000000000000 : ℚ),
    (-4647817797516221 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_3_correct (a b : Fin 4) :
    correctionCellCoefficient 20 3 a b = cellMatrix_20_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 3 a.val b.val = cellMatrix_20_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (20, 4). -/
def cellMatrix_20_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (92062861186412083 / 1800000000000000000 : ℚ),
    (-19434500739778403 / 600000000000000000 : ℚ),
    (-6746001388595591 / 600000000000000000 : ℚ),
    (2743059959078051 / 300000000000000000 : ℚ)
  ],
  ![
    (-22554842198683999 / 600000000000000000 : ℚ),
    (-1270119818491921 / 200000000000000000 : ℚ),
    (609784546427407 / 40000000000000000 : ℚ),
    (-18681049688177 / 20000000000000000 : ℚ)
  ],
  ![
    (-3986999185642559 / 600000000000000000 : ℚ),
    (3410261988089599 / 200000000000000000 : ℚ),
    (7011784705629727 / 200000000000000000 : ℚ),
    (-650029197950153 / 25000000000000000 : ℚ)
  ],
  ![
    (484017683598667 / 60000000000000000 : ℚ),
    (-174294370304261 / 60000000000000000 : ℚ),
    (-615813658098289 / 25000000000000000 : ℚ),
    (26418656241373991 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_4_correct (a b : Fin 4) :
    correctionCellCoefficient 20 4 a b = cellMatrix_20_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 4 a.val b.val = cellMatrix_20_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (20, 5). -/
def cellMatrix_20_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (29979714555758407 / 1800000000000000000 : ℚ),
    (-5489381254167093 / 200000000000000000 : ℚ),
    (1942471673174543 / 120000000000000000 : ℚ),
    (-2111488555852811 / 600000000000000000 : ℚ)
  ],
  ![
    (-17778864948393967 / 600000000000000000 : ℚ),
    (4267294155136839 / 200000000000000000 : ℚ),
    (99539649659669 / 8000000000000000 : ℚ),
    (-1955461313268669 / 200000000000000000 : ℚ)
  ],
  ![
    (11678440144711747 / 600000000000000000 : ℚ),
    (1833130648545381 / 200000000000000000 : ℚ),
    (-1717783209034789 / 40000000000000000 : ℚ),
    (3988936247829409 / 200000000000000000 : ℚ)
  ],
  ![
    (-8628227742870637 / 1800000000000000000 : ℚ),
    (-1627781016795497 / 200000000000000000 : ℚ),
    (2327825689403011 / 120000000000000000 : ℚ),
    (-1668557905036593 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_20_5_correct (a b : Fin 4) :
    correctionCellCoefficient 20 5 a b = cellMatrix_20_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 20 5 a.val b.val = cellMatrix_20_5 a b) a b

end PartialBalayage.Maximal.Square
