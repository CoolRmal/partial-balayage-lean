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

/-- Candidate finite rational coefficient matrix on cell (10, 5). -/
def cellMatrix_10_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (11314475487045263 / 112500000000000000 : ℚ),
    (8080182890325283 / 300000000000000000 : ℚ),
    (-519066177657623 / 75000000000000000 : ℚ),
    (-14240224210033 / 22500000000000000 : ℚ)
  ],
  ![
    (3489336175257653 / 150000000000000000 : ℚ),
    (-255078062885763 / 20000000000000000 : ℚ),
    (30456251850653 / 50000000000000000 : ℚ),
    (38511680783 / 1200000000000000 : ℚ)
  ],
  ![
    (-768017998790467 / 150000000000000000 : ℚ),
    (264093069956329 / 100000000000000000 : ℚ),
    (-2864940675421 / 50000000000000000 : ℚ),
    (19626789172669 / 150000000000000000 : ℚ)
  ],
  ![
    (46349893255873 / 37500000000000000 : ℚ),
    (-1333865563219 / 12500000000000000 : ℚ),
    (3936370867727 / 50000000000000000 : ℚ),
    (-88450311736759 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_5_correct (a b : Fin 4) :
    correctionCellCoefficient 10 5 a b = cellMatrix_10_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 5 a.val b.val = cellMatrix_10_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 6). -/
def cellMatrix_10_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (11995327718560573 / 100000000000000000 : ℚ),
    (3358044500662979 / 300000000000000000 : ℚ),
    (-220489473252651 / 25000000000000000 : ℚ),
    (-72240262713941 / 180000000000000000 : ℚ)
  ],
  ![
    (1114955612842843 / 100000000000000000 : ℚ),
    (-1143937386830453 / 100000000000000000 : ℚ),
    (2204388246783 / 3125000000000000 : ℚ),
    (-112696800843229 / 300000000000000000 : ℚ)
  ],
  ![
    (-48112856894609 / 20000000000000000 : ℚ),
    (291886885599983 / 100000000000000000 : ℚ),
    (523807765539 / 1562500000000000 : ℚ),
    (37735124205107 / 300000000000000000 : ℚ)
  ],
  ![
    (2085977274679781 / 1800000000000000000 : ℚ),
    (-58002957945823 / 600000000000000000 : ℚ),
    (-8242772264807 / 120000000000000000 : ℚ),
    (139596518686043 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_6_correct (a b : Fin 4) :
    correctionCellCoefficient 10 6 a b = cellMatrix_10_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 6 a.val b.val = cellMatrix_10_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 7). -/
def cellMatrix_10_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (109733260618368953 / 900000000000000000 : ℚ),
    (-45898083419407 / 6000000000000000 : ℚ),
    (-3007074992601517 / 300000000000000000 : ℚ),
    (-94677246788001 / 40000000000000000 : ℚ)
  ],
  ![
    (11979148885109 / 300000000000000000 : ℚ),
    (-111555333987957 / 10000000000000000 : ℚ),
    (-42156376946173 / 100000000000000000 : ℚ),
    (-115581199474251 / 200000000000000000 : ℚ)
  ],
  ![
    (292274018569409 / 300000000000000000 : ℚ),
    (198334701897041 / 50000000000000000 : ℚ),
    (71258821199603 / 100000000000000000 : ℚ),
    (309100543933697 / 200000000000000000 : ℚ)
  ],
  ![
    (308467733689 / 288000000000000 : ℚ),
    (-16683238157 / 12000000000000000 : ℚ),
    (12297832170251 / 75000000000000000 : ℚ),
    (-936077464216583 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_7_correct (a b : Fin 4) :
    correctionCellCoefficient 10 7 a b = cellMatrix_10_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 7 a.val b.val = cellMatrix_10_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 8). -/
def cellMatrix_10_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (183394170149846659 / 1800000000000000000 : ℚ),
    (-20878584417806813 / 600000000000000000 : ℚ),
    (-10274626090663079 / 600000000000000000 : ℚ),
    (-2630945813964569 / 200000000000000000 : ℚ)
  ],
  ![
    (-7269043601606993 / 600000000000000000 : ℚ),
    (-549295157193317 / 40000000000000000 : ℚ),
    (-431056352315099 / 200000000000000000 : ℚ),
    (-2197643043420109 / 600000000000000000 : ℚ)
  ],
  ![
    (4319419018902019 / 600000000000000000 : ℚ),
    (2005675724187667 / 200000000000000000 : ℚ),
    (1069819274200297 / 200000000000000000 : ℚ),
    (2873146587860193 / 200000000000000000 : ℚ)
  ],
  ![
    (1284491357702141 / 1800000000000000000 : ℚ),
    (-740146311400417 / 600000000000000000 : ℚ),
    (-33507792274183 / 24000000000000000 : ℚ),
    (-2548947583641437 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_8_correct (a b : Fin 4) :
    correctionCellCoefficient 10 8 a b = cellMatrix_10_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 8 a.val b.val = cellMatrix_10_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 9). -/
def cellMatrix_10_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (33128013149377931 / 900000000000000000 : ℚ),
    (-5425529077067841 / 50000000000000000 : ℚ),
    (-169765692081721 / 3000000000000000 : ℚ),
    (9177783618703211 / 225000000000000000 : ℚ)
  ],
  ![
    (-3166547176645359 / 100000000000000000 : ℚ),
    (-1451557883504223 / 50000000000000000 : ℚ),
    (-328587424466901 / 25000000000000000 : ℚ),
    (-101908539724989 / 4000000000000000 : ℚ)
  ],
  ![
    (2216534377764649 / 60000000000000000 : ℚ),
    (319118850904221 / 5000000000000000 : ℚ),
    (2422314759445219 / 50000000000000000 : ℚ),
    (-1001165049324283 / 12000000000000000 : ℚ)
  ],
  ![
    (-4548274110542861 / 600000000000000000 : ℚ),
    (-2522265251935063 / 120000000000000000 : ℚ),
    (-3677828380473441 / 200000000000000000 : ℚ),
    (95592125331097439 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_9_correct (a b : Fin 4) :
    correctionCellCoefficient 10 9 a b = cellMatrix_10_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 9 a.val b.val = cellMatrix_10_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (10, 10). -/
def cellMatrix_10_10 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-78750083387546663 / 900000000000000000 : ℚ),
    (-4965863067323067 / 50000000000000000 : ℚ),
    (2466820658330093 / 37500000000000000 : ℚ),
    (5506434398090971 / 900000000000000000 : ℚ)
  ],
  ![
    (-4965863067323067 / 50000000000000000 : ℚ),
    (-13174955642117829 / 100000000000000000 : ℚ),
    (-8957490177241779 / 100000000000000000 : ℚ),
    (10152304798096913 / 100000000000000000 : ℚ)
  ],
  ![
    (2466820658330093 / 37500000000000000 : ℚ),
    (-8957490177241779 / 100000000000000000 : ℚ),
    (-20184496714216637 / 100000000000000000 : ℚ),
    (21139660047419279 / 150000000000000000 : ℚ)
  ],
  ![
    (5506434398090971 / 900000000000000000 : ℚ),
    (10152304798096913 / 100000000000000000 : ℚ),
    (21139660047419279 / 150000000000000000 : ℚ),
    (-221432055732504103 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_10_10_correct (a b : Fin 4) :
    correctionCellCoefficient 10 10 a b = cellMatrix_10_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 10 10 a.val b.val = cellMatrix_10_10 a b) a b

end PartialBalayage.Maximal.Square
