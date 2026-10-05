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

/-- Candidate finite rational coefficient matrix on cell (15, 7). -/
def cellMatrix_15_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (219726199841031809 / 1800000000000000000 : ℚ),
    (-3926099966649591 / 200000000000000000 : ℚ),
    (-3052110453297277 / 600000000000000000 : ℚ),
    (-34353302576759 / 90000000000000000 : ℚ)
  ],
  ![
    (-10188188502068509 / 600000000000000000 : ℚ),
    (-923720749148631 / 200000000000000000 : ℚ),
    (147669000153473 / 200000000000000000 : ℚ),
    (-81194964594591 / 25000000000000000 : ℚ)
  ],
  ![
    (-2916696676433593 / 600000000000000000 : ℚ),
    (-27479029938231 / 200000000000000000 : ℚ),
    (434638462630313 / 200000000000000000 : ℚ),
    (-1556875288371641 / 300000000000000000 : ℚ)
  ],
  ![
    (-206479555580969 / 360000000000000000 : ℚ),
    (-2058714897274637 / 600000000000000000 : ℚ),
    (-2968610222509117 / 600000000000000000 : ℚ),
    (1563205387018211 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_7_correct (a b : Fin 4) :
    correctionCellCoefficient 15 7 a b = cellMatrix_15_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 7 a.val b.val = cellMatrix_15_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 8). -/
def cellMatrix_15_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (174547902729758479 / 1800000000000000000 : ℚ),
    (-6189862286026169 / 200000000000000000 : ℚ),
    (-3739176504832457 / 600000000000000000 : ℚ),
    (-54627883472123 / 100000000000000000 : ℚ)
  ],
  ![
    (-14465022899324167 / 600000000000000000 : ℚ),
    (-2577061899111869 / 200000000000000000 : ℚ),
    (-1801010150116711 / 200000000000000000 : ℚ),
    (2803239777678173 / 300000000000000000 : ℚ)
  ],
  ![
    (-4808968955100629 / 600000000000000000 : ℚ),
    (-2271952681420887 / 200000000000000000 : ℚ),
    (-2679112114112969 / 200000000000000000 : ℚ),
    (889035373777913 / 50000000000000000 : ℚ)
  ],
  ![
    (-127845290880763 / 112500000000000000 : ℚ),
    (1518228285217757 / 150000000000000000 : ℚ),
    (5550119130327391 / 300000000000000000 : ℚ),
    (-7191425152978237 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_8_correct (a b : Fin 4) :
    correctionCellCoefficient 15 8 a b = cellMatrix_15_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 8 a.val b.val = cellMatrix_15_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 9). -/
def cellMatrix_15_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (106638310738527373 / 1800000000000000000 : ℚ),
    (-5406248354048327 / 120000000000000000 : ℚ),
    (-4722478407330671 / 600000000000000000 : ℚ),
    (5972022353531101 / 600000000000000000 : ℚ)
  ],
  ![
    (-7330919830551187 / 200000000000000000 : ℚ),
    (-114520528797789 / 40000000000000000 : ℚ),
    (761093881047927 / 40000000000000000 : ℚ),
    (-2738631350341459 / 600000000000000000 : ℚ)
  ],
  ![
    (-8993738856367241 / 600000000000000000 : ℚ),
    (3038247575688131 / 200000000000000000 : ℚ),
    (7989312371221987 / 200000000000000000 : ℚ),
    (-5395454593400189 / 200000000000000000 : ℚ)
  ],
  ![
    (10354114469286137 / 900000000000000000 : ℚ),
    (-123077737433089 / 150000000000000000 : ℚ),
    (-8832731175629083 / 300000000000000000 : ℚ),
    (7356905109319237 / 450000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_9_correct (a b : Fin 4) :
    correctionCellCoefficient 15 9 a b = cellMatrix_15_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 9 a.val b.val = cellMatrix_15_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 10). -/
def cellMatrix_15_10 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (14646608633201879 / 900000000000000000 : ℚ),
    (-9280065762154837 / 300000000000000000 : ℚ),
    (1649198581657829 / 75000000000000000 : ℚ),
    (-10510317217739111 / 1800000000000000000 : ℚ)
  ],
  ![
    (-300655811164859 / 12000000000000000 : ℚ),
    (2149852408074433 / 100000000000000000 : ℚ),
    (2083668075973 / 390625000000000 : ℚ),
    (-3750109490421697 / 600000000000000000 : ℚ)
  ],
  ![
    (3951288602081273 / 300000000000000000 : ℚ),
    (1415254268965769 / 100000000000000000 : ℚ),
    (-409852570448929 / 10000000000000000 : ℚ),
    (10880322844502101 / 600000000000000000 : ℚ)
  ],
  ![
    (-542183815890293 / 225000000000000000 : ℚ),
    (-319780760748587 / 30000000000000000 : ℚ),
    (5881079043009391 / 300000000000000000 : ℚ),
    (-14445429521542303 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_10_correct (a b : Fin 4) :
    correctionCellCoefficient 15 10 a b = cellMatrix_15_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 10 a.val b.val = cellMatrix_15_10 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 11). -/
def cellMatrix_15_11 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (2683271435523521 / 1800000000000000000 : ℚ),
    (-2683271435523521 / 600000000000000000 : ℚ),
    (2683271435523521 / 600000000000000000 : ℚ),
    (-2683271435523521 / 1800000000000000000 : ℚ)
  ],
  ![
    (-2683271435523521 / 600000000000000000 : ℚ),
    (2683271435523521 / 200000000000000000 : ℚ),
    (-2683271435523521 / 200000000000000000 : ℚ),
    (2683271435523521 / 600000000000000000 : ℚ)
  ],
  ![
    (2683271435523521 / 600000000000000000 : ℚ),
    (-2683271435523521 / 200000000000000000 : ℚ),
    (2683271435523521 / 200000000000000000 : ℚ),
    (-2683271435523521 / 600000000000000000 : ℚ)
  ],
  ![
    (-2683271435523521 / 1800000000000000000 : ℚ),
    (2683271435523521 / 600000000000000000 : ℚ),
    (-2683271435523521 / 600000000000000000 : ℚ),
    (2683271435523521 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_15_11_correct (a b : Fin 4) :
    correctionCellCoefficient 15 11 a b = cellMatrix_15_11 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 11 a.val b.val = cellMatrix_15_11 a b) a b

/-- Candidate finite rational coefficient matrix on cell (15, 12). -/
def cellMatrix_15_12 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_15_12_correct (a b : Fin 4) :
    correctionCellCoefficient 15 12 a b = cellMatrix_15_12 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 15 12 a.val b.val = cellMatrix_15_12 a b) a b

end PartialBalayage.Maximal.Square
