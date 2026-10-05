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

/-- Candidate finite rational coefficient matrix on cell (3, 0). -/
def cellMatrix_3_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-107176915852613269 / 50000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-51242951650016723 / 50000000000000000 : ℚ),
    (110053300590626099 / 300000000000000000 : ℚ)
  ],
  ![
    (87818894674696333 / 75000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (4464122669540191 / 6250000000000000 : ℚ),
    (-15889252515864949 / 150000000000000000 : ℚ)
  ],
  ![
    (-1948217983248093 / 5000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-913562348890179 / 10000000000000000 : ℚ),
    (-3450105573169711 / 20000000000000000 : ℚ)
  ],
  ![
    (24673656572515357 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-2023763238858277 / 50000000000000000 : ℚ),
    (82349091781899613 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_3_0_correct (a b : Fin 4) :
    correctionCellCoefficient 3 0 a b = cellMatrix_3_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 3 0 a.val b.val = cellMatrix_3_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (3, 1). -/
def cellMatrix_3_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-840465904425153853 / 300000000000000000 : ℚ),
    (-94918506009440793 / 100000000000000000 : ℚ),
    (7567397290592653 / 100000000000000000 : ℚ),
    (19014556237527203 / 200000000000000000 : ℚ)
  ],
  ![
    (266887480902492301 / 150000000000000000 : ℚ),
    (55536710196778107 / 50000000000000000 : ℚ),
    (19823728840456579 / 50000000000000000 : ℚ),
    (-160705479888464737 / 200000000000000000 : ℚ)
  ],
  ![
    (-13070102203942441 / 20000000000000000 : ℚ),
    (-14004566115069849 / 20000000000000000 : ℚ),
    (-12177441417289491 / 20000000000000000 : ℚ),
    (211461579760481691 / 200000000000000000 : ℚ)
  ],
  ![
    (59971161599998349 / 450000000000000000 : ℚ),
    (58063932915600289 / 300000000000000000 : ℚ),
    (70206512348749951 / 300000000000000000 : ℚ),
    (-177111664854215867 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_3_1_correct (a b : Fin 4) :
    correctionCellCoefficient 3 1 a b = cellMatrix_3_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 3 1 a.val b.val = cellMatrix_3_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (3, 2). -/
def cellMatrix_3_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-2147994792450814937 / 600000000000000000 : ℚ),
    (-20504750828785873 / 40000000000000000 : ℚ),
    (14435692658753383 / 40000000000000000 : ℚ),
    (23537477939432699 / 100000000000000000 : ℚ)
  ],
  ![
    (59590350095655649 / 24000000000000000 : ℚ),
    (-101379768154629151 / 200000000000000000 : ℚ),
    (-80564304860713579 / 40000000000000000 : ℚ),
    (57201924522380189 / 60000000000000000 : ℚ)
  ],
  ![
    (-181059517602536119 / 200000000000000000 : ℚ),
    (250790249784956763 / 200000000000000000 : ℚ),
    (512610325108550163 / 200000000000000000 : ℚ),
    (-184468863180303849 / 100000000000000000 : ℚ)
  ],
  ![
    (4181398035683769 / 25000000000000000 : ℚ),
    (-155746372095331543 / 300000000000000000 : ℚ),
    (-94672272453227261 / 100000000000000000 : ℚ),
    (347084775339123209 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_3_2_correct (a b : Fin 4) :
    correctionCellCoefficient 3 2 a b = cellMatrix_3_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 3 2 a.val b.val = cellMatrix_3_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (3, 3). -/
def cellMatrix_3_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-2097805797364706093 / 600000000000000000 : ℚ),
    (183058040080200659 / 200000000000000000 : ℚ),
    (213403330930363109 / 200000000000000000 : ℚ),
    (-118647422100544469 / 225000000000000000 : ℚ)
  ],
  ![
    (183058040080200659 / 200000000000000000 : ℚ),
    (-335003571537963051 / 200000000000000000 : ℚ),
    (33839544184046799 / 40000000000000000 : ℚ),
    (-9870152045482897 / 100000000000000000 : ℚ)
  ],
  ![
    (213403330930363109 / 200000000000000000 : ℚ),
    (33839544184046799 / 40000000000000000 : ℚ),
    (-594202853973272931 / 200000000000000000 : ℚ),
    (82030546663712927 / 60000000000000000 : ℚ)
  ],
  ![
    (-118647422100544469 / 225000000000000000 : ℚ),
    (-9870152045482897 / 100000000000000000 : ℚ),
    (82030546663712927 / 60000000000000000 : ℚ),
    (-1782682143299291 / 2500000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_3_3_correct (a b : Fin 4) :
    correctionCellCoefficient 3 3 a b = cellMatrix_3_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 3 3 a.val b.val = cellMatrix_3_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (4, 0). -/
def cellMatrix_4_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-76801067767852901 / 60000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-22121545277004367 / 50000000000000000 : ℚ),
    (161918727665951221 / 900000000000000000 : ℚ)
  ],
  ![
    (191510390426560243 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (20506068150844907 / 50000000000000000 : ℚ),
    (-10586516088984323 / 60000000000000000 : ℚ)
  ],
  ![
    (-14290703092446503 / 100000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-5319550730512863 / 25000000000000000 : ℚ),
    (7649377046088487 / 75000000000000000 : ℚ)
  ],
  ![
    (7069352177661313 / 450000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (15557467803451223 / 300000000000000000 : ℚ),
    (-24204094702683523 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_4_0_correct (a b : Fin 4) :
    correctionCellCoefficient 4 0 a b = cellMatrix_4_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 4 0 a.val b.val = cellMatrix_4_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (4, 1). -/
def cellMatrix_4_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-13882851038379209 / 9000000000000000 : ℚ),
    (-103539815658101183 / 300000000000000000 : ℚ),
    (29189456003925019 / 300000000000000000 : ℚ),
    (-16102150886193211 / 360000000000000000 : ℚ)
  ],
  ![
    (8720473962890269 / 10000000000000000 : ℚ),
    (29091692158458013 / 100000000000000000 : ℚ),
    (-11920444143231801 / 100000000000000000 : ℚ),
    (78206379480632467 / 600000000000000000 : ℚ)
  ],
  ![
    (-76109209859139917 / 300000000000000000 : ℚ),
    (-2989724414937239 / 25000000000000000 : ℚ),
    (291228289446953 / 3125000000000000 : ℚ),
    (-14812384027083679 / 120000000000000000 : ℚ)
  ],
  ![
    (9151753265748193 / 225000000000000000 : ℚ),
    (2303613634739641 / 100000000000000000 : ℚ),
    (-86466268992323 / 3000000000000000 : ℚ),
    (7965620216763439 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_4_1_correct (a b : Fin 4) :
    correctionCellCoefficient 4 1 a b = cellMatrix_4_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 4 1 a.val b.val = cellMatrix_4_1 a b) a b

end PartialBalayage.Maximal.Square
