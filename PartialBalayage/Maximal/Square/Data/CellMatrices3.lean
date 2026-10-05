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

/-- Candidate finite rational coefficient matrix on cell (5, 3). -/
def cellMatrix_5_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-200716848639066117 / 200000000000000000 : ℚ),
    (17896980597737863 / 600000000000000000 : ℚ),
    (8231759076908331 / 200000000000000000 : ℚ),
    (32179971487811243 / 600000000000000000 : ℚ)
  ],
  ![
    (416132718028221733 / 600000000000000000 : ℚ),
    (27042599776668709 / 200000000000000000 : ℚ),
    (10897645076132059 / 200000000000000000 : ℚ),
    (-28831769254266563 / 200000000000000000 : ℚ)
  ],
  ![
    (-51770875658978907 / 200000000000000000 : ℚ),
    (-27105166900275461 / 200000000000000000 : ℚ),
    (-16302447198541683 / 200000000000000000 : ℚ),
    (26290496983229641 / 200000000000000000 : ℚ)
  ],
  ![
    (16092552130473617 / 300000000000000000 : ℚ),
    (1597822572210593 / 37500000000000000 : ℚ),
    (2885837496684179 / 100000000000000000 : ℚ),
    (-25085899207716863 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_5_3_correct (a b : Fin 4) :
    correctionCellCoefficient 5 3 a b = cellMatrix_5_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 5 3 a.val b.val = cellMatrix_5_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (5, 4). -/
def cellMatrix_5_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-43948193050077021 / 50000000000000000 : ℚ),
    (81913724761310789 / 300000000000000000 : ℚ),
    (20205865282359787 / 100000000000000000 : ℚ),
    (-184234344690739843 / 1800000000000000000 : ℚ)
  ],
  ![
    (110864536205956087 / 150000000000000000 : ℚ),
    (-18828708916933431 / 100000000000000000 : ℚ),
    (-7559766268666763 / 20000000000000000 : ℚ),
    (118370584957978307 / 600000000000000000 : ℚ)
  ],
  ![
    (-6888799277456641 / 20000000000000000 : ℚ),
    (1197589353270631 / 12500000000000000 : ℚ),
    (1564226093778681 / 5000000000000000 : ℚ),
    (-101526594883313899 / 600000000000000000 : ℚ)
  ],
  ![
    (49979391188704933 / 600000000000000000 : ℚ),
    (-15062486507570953 / 600000000000000000 : ℚ),
    (-3862844842869701 / 40000000000000000 : ℚ),
    (47912551245036899 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_5_4_correct (a b : Fin 4) :
    correctionCellCoefficient 5 4 a b = cellMatrix_5_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 5 4 a.val b.val = cellMatrix_5_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (5, 5). -/
def cellMatrix_5_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-911181370843171699 / 1800000000000000000 : ℚ),
    (74021162740066393 / 200000000000000000 : ℚ),
    (-62999152996581121 / 600000000000000000 : ℚ),
    (26747798604339193 / 1800000000000000000 : ℚ)
  ],
  ![
    (74021162740066393 / 200000000000000000 : ℚ),
    (-14096431649844763 / 40000000000000000 : ℚ),
    (42772922271310677 / 200000000000000000 : ℚ),
    (-2341515286905879 / 40000000000000000 : ℚ)
  ],
  ![
    (-62999152996581121 / 600000000000000000 : ℚ),
    (42772922271310677 / 200000000000000000 : ℚ),
    (-38957551132166659 / 200000000000000000 : ℚ),
    (37882429847028283 / 600000000000000000 : ℚ)
  ],
  ![
    (26747798604339193 / 1800000000000000000 : ℚ),
    (-2341515286905879 / 40000000000000000 : ℚ),
    (37882429847028283 / 600000000000000000 : ℚ),
    (-19555067482687147 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_5_5_correct (a b : Fin 4) :
    correctionCellCoefficient 5 5 a b = cellMatrix_5_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 5 5 a.val b.val = cellMatrix_5_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (6, 0). -/
def cellMatrix_6_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-10165616425186519 / 22500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-7356492135545989 / 75000000000000000 : ℚ),
    (75825506778068557 / 1800000000000000000 : ℚ)
  ],
  ![
    (18565366043739277 / 75000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (62383737739999 / 1000000000000000 : ℚ),
    (-14613517432812719 / 600000000000000000 : ℚ)
  ],
  ![
    (-845500356511493 / 15000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-513522342109501 / 25000000000000000 : ℚ),
    (896594632328183 / 120000000000000000 : ℚ)
  ],
  ![
    (3421970457299447 / 450000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (1036617853650223 / 300000000000000000 : ℚ),
    (-694811939776553 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_6_0_correct (a b : Fin 4) :
    correctionCellCoefficient 6 0 a b = cellMatrix_6_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 6 0 a.val b.val = cellMatrix_6_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (6, 1). -/
def cellMatrix_6_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-913979618489956699 / 1800000000000000000 : ℚ),
    (-13959455796889089 / 200000000000000000 : ℚ),
    (3394713938740129 / 120000000000000000 : ℚ),
    (87877113002617 / 37500000000000000 : ℚ)
  ],
  ![
    (57113217853700299 / 200000000000000000 : ℚ),
    (10339977663186881 / 200000000000000000 : ℚ),
    (-2136769884812919 / 200000000000000000 : ℚ),
    (-142502067051827 / 150000000000000000 : ℚ)
  ],
  ![
    (-41661577309446829 / 600000000000000000 : ℚ),
    (-3733384312111101 / 200000000000000000 : ℚ),
    (374794424764907 / 200000000000000000 : ℚ),
    (2350729639459 / 50000000000000000 : ℚ)
  ],
  ![
    (17823153131769467 / 1800000000000000000 : ℚ),
    (2062035595271233 / 600000000000000000 : ℚ),
    (-11200112029213 / 600000000000000000 : ℚ),
    (47075377067 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_6_1_correct (a b : Fin 4) :
    correctionCellCoefficient 6 1 a b = cellMatrix_6_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 6 1 a.val b.val = cellMatrix_6_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (6, 2). -/
def cellMatrix_6_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-984475910156730949 / 1800000000000000000 : ℚ),
    (-3713126579140361 / 600000000000000000 : ℚ),
    (21191671117826261 / 600000000000000000 : ℚ),
    (2302112362887467 / 900000000000000000 : ℚ)
  ],
  ![
    (7815170745120619 / 24000000000000000 : ℚ),
    (1099285925070747 / 40000000000000000 : ℚ),
    (-2706778153020227 / 200000000000000000 : ℚ),
    (-280907697971001 / 100000000000000000 : ℚ)
  ],
  ![
    (-51709138215811903 / 600000000000000000 : ℚ),
    (-2955586706907779 / 200000000000000000 : ℚ),
    (80600636087683 / 40000000000000000 : ℚ),
    (38098412570311 / 37500000000000000 : ℚ)
  ],
  ![
    (11987853328436297 / 900000000000000000 : ℚ),
    (1019841223294937 / 300000000000000000 : ℚ),
    (-5576518326073 / 300000000000000000 : ℚ),
    (-266628882232201 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_6_2_correct (a b : Fin 4) :
    correctionCellCoefficient 6 2 a b = cellMatrix_6_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 6 2 a.val b.val = cellMatrix_6_2 a b) a b

end PartialBalayage.Maximal.Square
