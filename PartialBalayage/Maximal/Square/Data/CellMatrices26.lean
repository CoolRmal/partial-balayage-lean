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

/-- Candidate finite rational coefficient matrix on cell (18, 1). -/
def cellMatrix_18_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (996240784227011 / 9000000000000000 : ℚ),
    (10486849950137 / 18750000000000000 : ℚ),
    (202324396246583 / 300000000000000000 : ℚ),
    (-75473676883027 / 150000000000000000 : ℚ)
  ],
  ![
    (-2455792523886919 / 300000000000000000 : ℚ),
    (-114925867107567 / 100000000000000000 : ℚ),
    (-37064281367531 / 50000000000000000 : ℚ),
    (747681550679 / 150000000000000000 : ℚ)
  ],
  ![
    (-207678083801807 / 150000000000000000 : ℚ),
    (-1547898084331 / 10000000000000000 : ℚ),
    (-15218521710001 / 100000000000000000 : ℚ),
    (7784035615729 / 100000000000000000 : ℚ)
  ],
  ![
    (76120685097379 / 1800000000000000000 : ℚ),
    (-1619112505061 / 120000000000000000 : ℚ),
    (62641427146363 / 600000000000000000 : ℚ),
    (-46148686317191 / 360000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_1_correct (a b : Fin 4) :
    correctionCellCoefficient 18 1 a b = cellMatrix_18_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 1 a.val b.val = cellMatrix_18_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 2). -/
def cellMatrix_18_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (100281578347749263 / 900000000000000000 : ℚ),
    (9966360866433 / 25000000000000000 : ℚ),
    (-250517665051579 / 300000000000000000 : ℚ),
    (-264895791720479 / 600000000000000000 : ℚ)
  ],
  ![
    (-125894185429727 / 12500000000000000 : ℚ),
    (-261687629476333 / 100000000000000000 : ℚ),
    (-9079149954213 / 12500000000000000 : ℚ),
    (-103703003393413 / 600000000000000000 : ℚ)
  ],
  ![
    (-12102414210409 / 7500000000000000 : ℚ),
    (-180511339329 / 800000000000000 : ℚ),
    (4066792568593 / 50000000000000000 : ℚ),
    (-49061251324569 / 200000000000000000 : ℚ)
  ],
  ![
    (1502474562433 / 300000000000000000 : ℚ),
    (-18926023303089 / 100000000000000000 : ℚ),
    (-7004250184983 / 25000000000000000 : ℚ),
    (79902076018661 / 225000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_2_correct (a b : Fin 4) :
    correctionCellCoefficient 18 2 a b = cellMatrix_18_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 2 a.val b.val = cellMatrix_18_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 3). -/
def cellMatrix_18_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (198982941312410791 / 1800000000000000000 : ℚ),
    (-1557565374573361 / 600000000000000000 : ℚ),
    (-259144541052919 / 120000000000000000 : ℚ),
    (-1261474048461367 / 1800000000000000000 : ℚ)
  ],
  ![
    (-8152548878680531 / 600000000000000000 : ℚ),
    (-183522212176179 / 40000000000000000 : ℚ),
    (-248969402660821 / 200000000000000000 : ℚ),
    (77661491682631 / 200000000000000000 : ℚ)
  ],
  ![
    (-1201958884480061 / 600000000000000000 : ℚ),
    (-159777248257213 / 200000000000000000 : ℚ),
    (-26183316739867 / 40000000000000000 : ℚ),
    (498892265108087 / 600000000000000000 : ℚ)
  ],
  ![
    (-49185744312623 / 450000000000000000 : ℚ),
    (18945645945157 / 60000000000000000 : ℚ),
    (1840291420741 / 2343750000000000 : ℚ),
    (-499419441460451 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_3_correct (a b : Fin 4) :
    correctionCellCoefficient 18 3 a b = cellMatrix_18_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 3 a.val b.val = cellMatrix_18_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 4). -/
def cellMatrix_18_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (15763466918702963 / 150000000000000000 : ℚ),
    (-901747472260653 / 100000000000000000 : ℚ),
    (-426199458954327 / 100000000000000000 : ℚ),
    (-237607144328599 / 225000000000000000 : ℚ)
  ],
  ![
    (-5709652897128893 / 300000000000000000 : ℚ),
    (-295641347788661 / 50000000000000000 : ℚ),
    (-1951285109 / 24414062500000 : ℚ),
    (-470193781786711 / 150000000000000000 : ℚ)
  ],
  ![
    (-262524685873603 / 100000000000000000 : ℚ),
    (19320462363051 / 50000000000000000 : ℚ),
    (22998480088047 / 12500000000000000 : ℚ),
    (-689820592391723 / 150000000000000000 : ℚ)
  ],
  ![
    (-6057732182647 / 9000000000000000 : ℚ),
    (-19425322728039 / 6250000000000000 : ℚ),
    (-252540204505301 / 60000000000000000 : ℚ),
    (12599445748002941 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_4_correct (a b : Fin 4) :
    correctionCellCoefficient 18 4 a b = cellMatrix_18_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 4 a.val b.val = cellMatrix_18_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 5). -/
def cellMatrix_18_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (40839425276984281 / 450000000000000000 : ℚ),
    (-6212867747822317 / 300000000000000000 : ℚ),
    (-2229026954177377 / 300000000000000000 : ℚ),
    (-477187117750381 / 300000000000000000 : ℚ)
  ],
  ![
    (-8447865938853673 / 300000000000000000 : ℚ),
    (-193456898345459 / 12500000000000000 : ℚ),
    (-474190013689943 / 50000000000000000 : ℚ),
    (468694386362161 / 50000000000000000 : ℚ)
  ],
  ![
    (-1499328946112821 / 300000000000000000 : ℚ),
    (-60814036165537 / 6250000000000000 : ℚ),
    (-119565334407907 / 10000000000000000 : ℚ),
    (1765702369691711 / 100000000000000000 : ℚ)
  ],
  ![
    (-594266589786907 / 600000000000000000 : ℚ),
    (5683810676005177 / 600000000000000000 : ℚ),
    (3358014567649977 / 200000000000000000 : ℚ),
    (-4603347331174247 / 300000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_5_correct (a b : Fin 4) :
    correctionCellCoefficient 18 5 a b = cellMatrix_18_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 5 a.val b.val = cellMatrix_18_5 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 6). -/
def cellMatrix_18_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (54921605094718337 / 900000000000000000 : ℚ),
    (-2017080501571369 / 50000000000000000 : ℚ),
    (-91514707685713 / 7500000000000000 : ℚ),
    (19319921447854889 / 1800000000000000000 : ℚ)
  ],
  ![
    (-13123805263111381 / 300000000000000000 : ℚ),
    (-316124461675239 / 50000000000000000 : ℚ),
    (46594657269827 / 2500000000000000 : ℚ),
    (-1194783465169877 / 600000000000000000 : ℚ)
  ],
  ![
    (-1354127802610337 / 150000000000000000 : ℚ),
    (1932775842268401 / 100000000000000000 : ℚ),
    (4101453764996063 / 100000000000000000 : ℚ),
    (-720058544844619 / 24000000000000000 : ℚ)
  ],
  ![
    (5956893126819707 / 600000000000000000 : ℚ),
    (-1788185905140443 / 600000000000000000 : ℚ),
    (-5848680094698517 / 200000000000000000 : ℚ),
    (30977479862572433 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_6_correct (a b : Fin 4) :
    correctionCellCoefficient 18 6 a b = cellMatrix_18_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 6 a.val b.val = cellMatrix_18_6 a b) a b

end PartialBalayage.Maximal.Square
