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

/-- Candidate finite rational coefficient matrix on cell (6, 3). -/
def cellMatrix_6_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-61829070120993221 / 120000000000000000 : ℚ),
    (2884962692152473 / 40000000000000000 : ℚ),
    (1719726389573413 / 40000000000000000 : ℚ),
    (-88290755502731 / 100000000000000000 : ℚ)
  ],
  ![
    (202062776857189993 / 600000000000000000 : ℚ),
    (-64102914740509 / 8000000000000000 : ℚ),
    (-4392224340846233 / 200000000000000000 : ℚ),
    (-83542155970259 / 12500000000000000 : ℚ)
  ],
  ![
    (-19585771398031673 / 200000000000000000 : ℚ),
    (-1540005744905973 / 200000000000000000 : ℚ),
    (1012577781563391 / 200000000000000000 : ℚ),
    (602298887756389 / 100000000000000000 : ℚ)
  ],
  ![
    (9931555334817859 / 600000000000000000 : ℚ),
    (1750747491053381 / 600000000000000000 : ℚ),
    (-92593972961449 / 200000000000000000 : ℚ),
    (-1607224183257691 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_6_3_correct (a b : Fin 4) :
    correctionCellCoefficient 6 3 a b = cellMatrix_6_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 6 3 a.val b.val = cellMatrix_6_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (6, 4). -/
def cellMatrix_6_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-240604758912094201 / 600000000000000000 : ℚ),
    (31092332823480109 / 200000000000000000 : ℚ),
    (8068887414850679 / 200000000000000000 : ℚ),
    (-4208585775185869 / 200000000000000000 : ℚ)
  ],
  ![
    (180068361742540687 / 600000000000000000 : ℚ),
    (-14397045036777623 / 200000000000000000 : ℚ),
    (-1680449565483733 / 40000000000000000 : ℚ),
    (11142497681424307 / 600000000000000000 : ℚ)
  ],
  ![
    (-18908601585861477 / 200000000000000000 : ℚ),
    (4098943144759143 / 200000000000000000 : ℚ),
    (185054844324069 / 8000000000000000 : ℚ),
    (-1900497464413367 / 200000000000000000 : ℚ)
  ],
  ![
    (30999114354445297 / 1800000000000000000 : ℚ),
    (-134617647548713 / 40000000000000000 : ℚ),
    (-3492230285399729 / 600000000000000000 : ℚ),
    (341170778056439 / 150000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_6_4_correct (a b : Fin 4) :
    correctionCellCoefficient 6 4 a b = cellMatrix_6_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 6 4 a.val b.val = cellMatrix_6_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (6, 5). -/
def cellMatrix_6_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-33936713880664861 / 150000000000000000 : ℚ),
    (1730217516381193 / 10000000000000000 : ℚ),
    (-284804369419183 / 12500000000000000 : ℚ),
    (-4083234730714807 / 1800000000000000000 : ℚ)
  ],
  ![
    (12281298083137613 / 60000000000000000 : ℚ),
    (-10029521505095323 / 100000000000000000 : ℚ),
    (1370124927002821 / 100000000000000000 : ℚ),
    (510665141698029 / 200000000000000000 : ℚ)
  ],
  ![
    (-1510473099676747 / 25000000000000000 : ℚ),
    (1912548241930623 / 50000000000000000 : ℚ),
    (-134390160642297 / 25000000000000000 : ℚ),
    (-1227705118346011 / 600000000000000000 : ℚ)
  ],
  ![
    (18558678695231293 / 1800000000000000000 : ℚ),
    (-981935189470577 / 120000000000000000 : ℚ),
    (601819051277539 / 600000000000000000 : ℚ),
    (148968037024171 / 225000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_6_5_correct (a b : Fin 4) :
    correctionCellCoefficient 6 5 a b = cellMatrix_6_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 6 5 a.val b.val = cellMatrix_6_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (6, 6). -/
def cellMatrix_6_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-140896477546440751 / 1800000000000000000 : ℚ),
    (14477719357583041 / 120000000000000000 : ℚ),
    (-17753844462835591 / 600000000000000000 : ℚ),
    (758539144799847 / 200000000000000000 : ℚ)
  ],
  ![
    (14477719357583041 / 120000000000000000 : ℚ),
    (-521861915083411 / 8000000000000000 : ℚ),
    (4272245279099729 / 200000000000000000 : ℚ),
    (-838097849534813 / 200000000000000000 : ℚ)
  ],
  ![
    (-17753844462835591 / 600000000000000000 : ℚ),
    (4272245279099729 / 200000000000000000 : ℚ),
    (-2302826403484387 / 200000000000000000 : ℚ),
    (597854449156969 / 200000000000000000 : ℚ)
  ],
  ![
    (758539144799847 / 200000000000000000 : ℚ),
    (-838097849534813 / 200000000000000000 : ℚ),
    (597854449156969 / 200000000000000000 : ℚ),
    (-905737875261053 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_6_6_correct (a b : Fin 4) :
    correctionCellCoefficient 6 6 a b = cellMatrix_6_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 6 6 a.val b.val = cellMatrix_6_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (7, 0). -/
def cellMatrix_7_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-37954390826446687 / 150000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1055766498123203 / 20000000000000000 : ℚ),
    (21674719072611743 / 900000000000000000 : ℚ)
  ],
  ![
    (7880898471516047 / 50000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (633362578154823 / 20000000000000000 : ℚ),
    (-644333910738379 / 50000000000000000 : ℚ)
  ],
  ![
    (-1677677702605161 / 50000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1017471514787781 / 100000000000000000 : ℚ),
    (299817167788907 / 75000000000000000 : ℚ)
  ],
  ![
    (3705232517993179 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (265680507764237 / 150000000000000000 : ℚ),
    (-1244770389182459 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_0_correct (a b : Fin 4) :
    correctionCellCoefficient 7 0 a b = cellMatrix_7_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 0 a.val b.val = cellMatrix_7_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (7, 1). -/
def cellMatrix_7_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-126780559150806257 / 450000000000000000 : ℚ),
    (-9998275871084347 / 300000000000000000 : ℚ),
    (2919110800381849 / 150000000000000000 : ℚ),
    (2592749961901283 / 1800000000000000000 : ℚ)
  ],
  ![
    (17639942012329451 / 100000000000000000 : ℚ),
    (616905579279489 / 25000000000000000 : ℚ),
    (-699190573656159 / 100000000000000000 : ℚ),
    (-6847249086443 / 8000000000000000 : ℚ)
  ],
  ![
    (-11919212088838681 / 300000000000000000 : ℚ),
    (-417837179209967 / 50000000000000000 : ℚ),
    (181797156367847 / 100000000000000000 : ℚ),
    (1130233242023 / 24000000000000000 : ℚ)
  ],
  ![
    (3117953579991581 / 600000000000000000 : ℚ),
    (880673672931437 / 600000000000000000 : ℚ),
    (-60682786041837 / 200000000000000000 : ℚ),
    (3316570853923 / 120000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_7_1_correct (a b : Fin 4) :
    correctionCellCoefficient 7 1 a b = cellMatrix_7_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 7 1 a.val b.val = cellMatrix_7_1 a b) a b

end PartialBalayage.Maximal.Square
