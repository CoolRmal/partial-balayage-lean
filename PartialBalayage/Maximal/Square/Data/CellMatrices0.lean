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

/-- Candidate finite rational coefficient matrix on cell (0, 0). -/
def cellMatrix_0_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-2231451509561082241 / 90000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (4272954493350132607 / 150000000000000000 : ℚ),
    (-12484546856254210157 / 900000000000000000 : ℚ)
  ],
  ![
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ],
  ![
    (4272954493350132607 / 150000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-340992498652911263 / 5000000000000000 : ℚ),
    (549436948932703163 / 15000000000000000 : ℚ)
  ],
  ![
    (-12484546856254210157 / 900000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (549436948932703163 / 15000000000000000 : ℚ),
    (-18011598276544751507 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_0_0_correct (a b : Fin 4) :
    correctionCellCoefficient 0 0 a b = cellMatrix_0_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  norm_num (config := { maxSteps := 1000000 }) [localCellCoefficient,
    representativeCoefficient, cubicSplineCellCoefficient, splineOrbits,
    Finset.sum_range_succ, splineOrbits0, splineOrbits1, splineOrbits2,
    splineOrbits3, splineOrbits4, splineOrbits5, splineOrbits6, splineOrbits7,
    splineOrbits8, splineOrbits9, splineOrbits10, splineOrbits11, splineOrbits12]
  fin_cases a <;> fin_cases b <;> norm_num [cellMatrix_0_0]

/-- Candidate finite rational coefficient matrix on cell (1, 0). -/
def cellMatrix_1_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-40717044407841053 / 4000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-154150325636724551 / 50000000000000000 : ℚ),
    (617517950790807029 / 225000000000000000 : ℚ)
  ],
  ![
    (4607271117146320271 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-132548048373119363 / 5000000000000000 : ℚ),
    (1321959893587791671 / 100000000000000000 : ℚ)
  ],
  ![
    (-1312879289851314981 / 100000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (2084444502797919 / 50000000000000 : ℚ),
    (-7022859297890688247 / 300000000000000000 : ℚ)
  ],
  ![
    (767681114920918547 / 180000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-4887572231561790947 / 300000000000000000 : ℚ),
    (3424534258294901099 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_1_0_correct (a b : Fin 4) :
    correctionCellCoefficient 1 0 a b = cellMatrix_1_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  norm_num (config := { maxSteps := 1000000 }) [localCellCoefficient,
    representativeCoefficient, cubicSplineCellCoefficient, splineOrbits,
    Finset.sum_range_succ, splineOrbits0, splineOrbits1, splineOrbits2,
    splineOrbits3, splineOrbits4, splineOrbits5, splineOrbits6, splineOrbits7,
    splineOrbits8, splineOrbits9, splineOrbits10, splineOrbits11, splineOrbits12]
  fin_cases a <;> fin_cases b <;> norm_num [cellMatrix_1_0]

/-- Candidate finite rational coefficient matrix on cell (1, 1). -/
def cellMatrix_1_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-9465969050062050727 / 900000000000000000 : ℚ),
    (4845842933769793 / 2343750000000000 : ℚ),
    (154516984934288081 / 30000000000000000 : ℚ),
    (-1508650316229018239 / 600000000000000000 : ℚ)
  ],
  ![
    (4845842933769793 / 2343750000000000 : ℚ),
    (-1336042254161399507 / 100000000000000000 : ℚ),
    (1314918713300987753 / 100000000000000000 : ℚ),
    (-2427617634772658293 / 600000000000000000 : ℚ)
  ],
  ![
    (154516984934288081 / 30000000000000000 : ℚ),
    (1314918713300987753 / 100000000000000000 : ℚ),
    (-2853970292294850247 / 100000000000000000 : ℚ),
    (2449175609450307867 / 200000000000000000 : ℚ)
  ],
  ![
    (-1508650316229018239 / 600000000000000000 : ℚ),
    (-2427617634772658293 / 600000000000000000 : ℚ),
    (2449175609450307867 / 200000000000000000 : ℚ),
    (-10365732014613475897 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_1_1_correct (a b : Fin 4) :
    correctionCellCoefficient 1 1 a b = cellMatrix_1_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  norm_num (config := { maxSteps := 1000000 }) [localCellCoefficient,
    representativeCoefficient, cubicSplineCellCoefficient, splineOrbits,
    Finset.sum_range_succ, splineOrbits0, splineOrbits1, splineOrbits2,
    splineOrbits3, splineOrbits4, splineOrbits5, splineOrbits6, splineOrbits7,
    splineOrbits8, splineOrbits9, splineOrbits10, splineOrbits11, splineOrbits12]
  fin_cases a <;> fin_cases b <;> norm_num [cellMatrix_1_1]

/-- Candidate finite rational coefficient matrix on cell (2, 0). -/
def cellMatrix_2_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-1658514837191259103 / 450000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-1258690070981786033 / 300000000000000000 : ℚ),
    (3720937195037082323 / 1800000000000000000 : ℚ)
  ],
  ![
    (2368337302679263 / 1250000000000000 : ℚ),
    (0 / 1 : ℚ),
    (799244812167497793 / 100000000000000000 : ℚ),
    (-1012335512853832489 / 200000000000000000 : ℚ)
  ],
  ![
    (-6264518434334513 / 18750000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-718683225965952947 / 100000000000000000 : ℚ),
    (3076952695693129001 / 600000000000000000 : ℚ)
  ],
  ![
    (-4165196011383343 / 225000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (709547602477051157 / 300000000000000000 : ℚ),
    (-3180455862888220331 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_2_0_correct (a b : Fin 4) :
    correctionCellCoefficient 2 0 a b = cellMatrix_2_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  norm_num (config := { maxSteps := 1000000 }) [localCellCoefficient,
    representativeCoefficient, cubicSplineCellCoefficient, splineOrbits,
    Finset.sum_range_succ, splineOrbits0, splineOrbits1, splineOrbits2,
    splineOrbits3, splineOrbits4, splineOrbits5, splineOrbits6, splineOrbits7,
    splineOrbits8, splineOrbits9, splineOrbits10, splineOrbits11, splineOrbits12]
  fin_cases a <;> fin_cases b <;> norm_num [cellMatrix_2_0]

/-- Candidate finite rational coefficient matrix on cell (2, 1). -/
def cellMatrix_2_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-10465262579618670287 / 1800000000000000000 : ℚ),
    (-437941029630020603 / 200000000000000000 : ℚ),
    (1203557053073510257 / 600000000000000000 : ℚ),
    (-13195538256573469 / 180000000000000000 : ℚ)
  ],
  ![
    (965088079909845177 / 200000000000000000 : ℚ),
    (31994542021698741 / 40000000000000000 : ℚ),
    (-1438516914226501881 / 200000000000000000 : ℚ),
    (475426001828928253 / 150000000000000000 : ℚ)
  ],
  ![
    (-1435611250001293097 / 600000000000000000 : ℚ),
    (202219791829317213 / 200000000000000000 : ℚ),
    (1639586243761223107 / 200000000000000000 : ℚ),
    (-377275648282819037 / 75000000000000000 : ℚ)
  ],
  ![
    (1043508183883019867 / 1800000000000000000 : ℚ),
    (-114088484326671901 / 200000000000000000 : ℚ),
    (-1761360657934118017 / 600000000000000000 : ℚ),
    (3652589925543997369 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_2_1_correct (a b : Fin 4) :
    correctionCellCoefficient 2 1 a b = cellMatrix_2_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  norm_num (config := { maxSteps := 1000000 }) [localCellCoefficient,
    representativeCoefficient, cubicSplineCellCoefficient, splineOrbits,
    Finset.sum_range_succ, splineOrbits0, splineOrbits1, splineOrbits2,
    splineOrbits3, splineOrbits4, splineOrbits5, splineOrbits6, splineOrbits7,
    splineOrbits8, splineOrbits9, splineOrbits10, splineOrbits11, splineOrbits12]
  fin_cases a <;> fin_cases b <;> norm_num [cellMatrix_2_1]

/-- Candidate finite rational coefficient matrix on cell (2, 2). -/
def cellMatrix_2_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-1214224007737117737 / 200000000000000000 : ℚ),
    (192267126938244803 / 120000000000000000 : ℚ),
    (357200556835925189 / 200000000000000000 : ℚ),
    (-44855006203205109 / 50000000000000000 : ℚ)
  ],
  ![
    (192267126938244803 / 120000000000000000 : ℚ),
    (-163071422205759409 / 40000000000000000 : ℚ),
    (463187093089211131 / 200000000000000000 : ℚ),
    (-6637401353257949 / 18750000000000000 : ℚ)
  ],
  ![
    (357200556835925189 / 200000000000000000 : ℚ),
    (463187093089211131 / 200000000000000000 : ℚ),
    (-1378618942501329189 / 200000000000000000 : ℚ),
    (78801219483744973 / 25000000000000000 : ℚ)
  ],
  ![
    (-44855006203205109 / 50000000000000000 : ℚ),
    (-6637401353257949 / 18750000000000000 : ℚ),
    (78801219483744973 / 25000000000000000 : ℚ),
    (-499673741115283741 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_2_2_correct (a b : Fin 4) :
    correctionCellCoefficient 2 2 a b = cellMatrix_2_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  norm_num (config := { maxSteps := 1000000 }) [localCellCoefficient,
    representativeCoefficient, cubicSplineCellCoefficient, splineOrbits,
    Finset.sum_range_succ, splineOrbits0, splineOrbits1, splineOrbits2,
    splineOrbits3, splineOrbits4, splineOrbits5, splineOrbits6, splineOrbits7,
    splineOrbits8, splineOrbits9, splineOrbits10, splineOrbits11, splineOrbits12]
  fin_cases a <;> fin_cases b <;> norm_num [cellMatrix_2_2]

end PartialBalayage.Maximal.Square
