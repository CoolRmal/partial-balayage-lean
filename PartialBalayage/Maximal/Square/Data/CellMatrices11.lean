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

/-- Candidate finite rational coefficient matrix on cell (11, 0). -/
def cellMatrix_11_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (12069253976447173 / 225000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-206996810821321 / 37500000000000000 : ℚ),
    (7077454332635797 / 1800000000000000000 : ℚ)
  ],
  ![
    (4880822968163467 / 150000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (32603733437339 / 10000000000000000 : ℚ),
    (-62596871971291 / 40000000000000000 : ℚ)
  ],
  ![
    (-71415353191237 / 15000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-2999235003511 / 5000000000000000 : ℚ),
    (1158978516263 / 4800000000000000 : ℚ)
  ],
  ![
    (18175162804547 / 90000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (275630250269 / 30000000000000000 : ℚ),
    (13134130011673 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_0_correct (a b : Fin 4) :
    correctionCellCoefficient 11 0 a b = cellMatrix_11_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 0 a.val b.val = cellMatrix_11_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 1). -/
def cellMatrix_11_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (10410626580532197 / 200000000000000000 : ℚ),
    (18142255454141 / 24000000000000000 : ℚ),
    (1255168453164887 / 200000000000000000 : ℚ),
    (-36253824329931 / 100000000000000000 : ℚ)
  ],
  ![
    (20540562799324843 / 600000000000000000 : ℚ),
    (73039251584839 / 40000000000000000 : ℚ),
    (-57375682164517 / 40000000000000000 : ℚ),
    (-259690596463 / 2000000000000000 : ℚ)
  ],
  ![
    (-40955333513839 / 8000000000000000 : ℚ),
    (-19013297149601 / 40000000000000000 : ℚ),
    (4980582878487 / 40000000000000000 : ℚ),
    (153742302693 / 1250000000000000 : ℚ)
  ],
  ![
    (393175201118753 / 1800000000000000000 : ℚ),
    (8053113340811 / 200000000000000000 : ℚ),
    (18646735017053 / 600000000000000000 : ℚ),
    (-29371796455957 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_1_correct (a b : Fin 4) :
    correctionCellCoefficient 11 1 a b = cellMatrix_11_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 1 a.val b.val = cellMatrix_11_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 2). -/
def cellMatrix_11_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (35233418541465191 / 600000000000000000 : ℚ),
    (7331998267404089 / 600000000000000000 : ℚ),
    (1037645507185301 / 200000000000000000 : ℚ),
    (-314243941842059 / 600000000000000000 : ℚ)
  ],
  ![
    (20697609161690773 / 600000000000000000 : ℚ),
    (-2291741941279 / 1600000000000000 : ℚ),
    (-72957117952297 / 40000000000000000 : ℚ),
    (2189995647667 / 200000000000000000 : ℚ)
  ],
  ![
    (-213889628154133 / 40000000000000000 : ℚ),
    (5707129665901 / 40000000000000000 : ℚ),
    (3947968787403 / 8000000000000000 : ℚ),
    (-12042578127399 / 200000000000000000 : ℚ)
  ],
  ![
    (21673901843467 / 90000000000000000 : ℚ),
    (-6665644827833 / 150000000000000000 : ℚ),
    (-34734327175409 / 300000000000000000 : ℚ),
    (23192460784177 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_2_correct (a b : Fin 4) :
    correctionCellCoefficient 11 2 a b = cellMatrix_11_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 2 a.val b.val = cellMatrix_11_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 3). -/
def cellMatrix_11_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (11341027347145781 / 150000000000000000 : ℚ),
    (6307569742494859 / 300000000000000000 : ℚ),
    (361700782671621 / 100000000000000000 : ℚ),
    (-2661499784776141 / 1800000000000000000 : ℚ)
  ],
  ![
    (9375209575684847 / 300000000000000000 : ℚ),
    (-252367233809961 / 50000000000000000 : ℚ),
    (-89553900704621 / 50000000000000000 : ℚ),
    (189769957608251 / 600000000000000000 : ℚ)
  ],
  ![
    (-238563962720871 / 50000000000000000 : ℚ),
    (94903176658729 / 100000000000000000 : ℚ),
    (31285742651439 / 100000000000000000 : ℚ),
    (25431547970507 / 600000000000000000 : ℚ)
  ],
  ![
    (214661718235421 / 1800000000000000000 : ℚ),
    (-96022505660437 / 600000000000000000 : ℚ),
    (108728001713 / 600000000000000000 : ℚ),
    (-72534472591987 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_3_correct (a b : Fin 4) :
    correctionCellCoefficient 11 3 a b = cellMatrix_11_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 3 a.val b.val = cellMatrix_11_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 4). -/
def cellMatrix_11_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (177786860924031563 / 1800000000000000000 : ℚ),
    (14294049092273029 / 600000000000000000 : ℚ),
    (-98259017749283 / 120000000000000000 : ℚ),
    (-364766905333229 / 200000000000000000 : ℚ)
  ],
  ![
    (4945711831600987 / 200000000000000000 : ℚ),
    (-1536130183268561 / 200000000000000000 : ℚ),
    (-168445645210233 / 200000000000000000 : ℚ),
    (104862525874067 / 200000000000000000 : ℚ)
  ],
  ![
    (-2080202488818937 / 600000000000000000 : ℚ),
    (340380871893721 / 200000000000000000 : ℚ),
    (17600606654677 / 40000000000000000 : ℚ),
    (-3481756370823 / 40000000000000000 : ℚ)
  ],
  ![
    (-72807043666369 / 900000000000000000 : ℚ),
    (-84169761124499 / 300000000000000000 : ℚ),
    (-36212872295137 / 300000000000000000 : ℚ),
    (1399320948103 / 150000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_4_correct (a b : Fin 4) :
    correctionCellCoefficient 11 4 a b = cellMatrix_11_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 4 a.val b.val = cellMatrix_11_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (11, 5). -/
def cellMatrix_11_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (26989027598326543 / 225000000000000000 : ℚ),
    (5014278383390569 / 300000000000000000 : ℚ),
    (-943549309186369 / 150000000000000000 : ℚ),
    (-311459752430957 / 600000000000000000 : ℚ)
  ],
  ![
    (167299926449813 / 10000000000000000 : ℚ),
    (-779216948033413 / 100000000000000000 : ℚ),
    (2283467693937 / 3125000000000000 : ℚ),
    (87819842036093 / 600000000000000000 : ℚ)
  ],
  ![
    (-211819279719991 / 150000000000000000 : ℚ),
    (232080296439073 / 100000000000000000 : ℚ),
    (111802149097 / 625000000000000 : ℚ),
    (-3314385015361 / 200000000000000000 : ℚ)
  ],
  ![
    (-425559018236659 / 900000000000000000 : ℚ),
    (-29639916005231 / 60000000000000000 : ℚ),
    (-27816946606519 / 300000000000000000 : ℚ),
    (29245856223193 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_11_5_correct (a b : Fin 4) :
    correctionCellCoefficient 11 5 a b = cellMatrix_11_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 11 5 a.val b.val = cellMatrix_11_5 a b) a b

end PartialBalayage.Maximal.Square
