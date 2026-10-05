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

/-- Candidate finite rational coefficient matrix on cell (17, 6). -/
def cellMatrix_17_6 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (58129908560005039 / 600000000000000000 : ℚ),
    (-14676882427418593 / 600000000000000000 : ℚ),
    (-305685495563007 / 40000000000000000 : ℚ),
    (-1101480816397933 / 900000000000000000 : ℚ)
  ],
  ![
    (-5822601882858089 / 200000000000000000 : ℚ),
    (-3133536213499121 / 200000000000000000 : ℚ),
    (-1988131814592129 / 200000000000000000 : ℚ),
    (2955493194937517 / 300000000000000000 : ℚ)
  ],
  ![
    (-1121097889069049 / 200000000000000000 : ℚ),
    (-1996513317738637 / 200000000000000000 : ℚ),
    (-2487203133813837 / 200000000000000000 : ℚ),
    (2723923441517641 / 150000000000000000 : ℚ)
  ],
  ![
    (-2053217543234201 / 1800000000000000000 : ℚ),
    (5862065002275439 / 600000000000000000 : ℚ),
    (10690110663805963 / 600000000000000000 : ℚ),
    (-28897157387186039 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_6_correct (a b : Fin 4) :
    correctionCellCoefficient 17 6 a b = cellMatrix_17_6 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 6 a.val b.val = cellMatrix_17_6 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 7). -/
def cellMatrix_17_7 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (114400269464628157 / 1800000000000000000 : ℚ),
    (-8683469642368223 / 200000000000000000 : ℚ),
    (-6788244066240971 / 600000000000000000 : ℚ),
    (19428811471108423 / 1800000000000000000 : ℚ)
  ],
  ![
    (-26921823342972983 / 600000000000000000 : ℚ),
    (-239762690561669 / 40000000000000000 : ℚ),
    (784570915056581 / 40000000000000000 : ℚ),
    (-1506116044714817 / 600000000000000000 : ℚ)
  ],
  ![
    (-1183749851158801 / 120000000000000000 : ℚ),
    (3924774180704253 / 200000000000000000 : ℚ),
    (8408490632256727 / 200000000000000000 : ℚ),
    (-3670776426108517 / 120000000000000000 : ℚ)
  ],
  ![
    (9353076033911983 / 900000000000000000 : ℚ),
    (-827435528649337 / 300000000000000000 : ℚ),
    (-4551761680845019 / 150000000000000000 : ℚ),
    (10638921568508273 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_7_correct (a b : Fin 4) :
    correctionCellCoefficient 17 7 a b = cellMatrix_17_7 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 7 a.val b.val = cellMatrix_17_7 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 8). -/
def cellMatrix_17_8 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (1765656097784983 / 90000000000000000 : ℚ),
    (-1683173799039849 / 50000000000000000 : ℚ),
    (3160141851216863 / 150000000000000000 : ℚ),
    (-738484026088507 / 150000000000000000 : ℚ)
  ],
  ![
    (-506395400506603 / 15000000000000000 : ℚ),
    (642597456630331 / 25000000000000000 : ℚ),
    (302092316321011 / 25000000000000000 : ℚ),
    (-387218601398341 / 37500000000000000 : ℚ)
  ],
  ![
    (254543261050927 / 12000000000000000 : ℚ),
    (1193936657337561 / 100000000000000000 : ℚ),
    (-4972695749142929 / 100000000000000000 : ℚ),
    (2287358431681871 / 100000000000000000 : ℚ)
  ],
  ![
    (-1792567313737493 / 360000000000000000 : ℚ),
    (-6152199798534007 / 600000000000000000 : ℚ),
    (13709717982144743 / 600000000000000000 : ℚ),
    (-17488477073950111 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_8_correct (a b : Fin 4) :
    correctionCellCoefficient 17 8 a b = cellMatrix_17_8 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 8 a.val b.val = cellMatrix_17_8 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 9). -/
def cellMatrix_17_9 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (472344886475671 / 225000000000000000 : ℚ),
    (-472344886475671 / 75000000000000000 : ℚ),
    (472344886475671 / 75000000000000000 : ℚ),
    (-472344886475671 / 225000000000000000 : ℚ)
  ],
  ![
    (-472344886475671 / 75000000000000000 : ℚ),
    (472344886475671 / 25000000000000000 : ℚ),
    (-472344886475671 / 25000000000000000 : ℚ),
    (472344886475671 / 75000000000000000 : ℚ)
  ],
  ![
    (472344886475671 / 75000000000000000 : ℚ),
    (-472344886475671 / 25000000000000000 : ℚ),
    (472344886475671 / 25000000000000000 : ℚ),
    (-472344886475671 / 75000000000000000 : ℚ)
  ],
  ![
    (-472344886475671 / 225000000000000000 : ℚ),
    (472344886475671 / 75000000000000000 : ℚ),
    (-472344886475671 / 75000000000000000 : ℚ),
    (472344886475671 / 225000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_17_9_correct (a b : Fin 4) :
    correctionCellCoefficient 17 9 a b = cellMatrix_17_9 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 9 a.val b.val = cellMatrix_17_9 a b) a b

/-- Candidate finite rational coefficient matrix on cell (17, 10). -/
def cellMatrix_17_10 : Fin 4 → Fin 4 → ℚ := ![
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
theorem cellMatrix_17_10_correct (a b : Fin 4) :
    correctionCellCoefficient 17 10 a b = cellMatrix_17_10 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 17 10 a.val b.val = cellMatrix_17_10 a b) a b

/-- Candidate finite rational coefficient matrix on cell (18, 0). -/
def cellMatrix_18_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (33163607873514433 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-11511599014797 / 100000000000000000 : ℚ),
    (118429596645487 / 450000000000000000 : ℚ)
  ],
  ![
    (-2300069352406847 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-8159460874501 / 20000000000000000 : ℚ),
    (-33331258362557 / 300000000000000000 : ℚ)
  ],
  ![
    (-26641115175133 / 20000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-260459133309 / 100000000000000000 : ℚ),
    (-3739515644173 / 75000000000000000 : ℚ)
  ],
  ![
    (9684577330897 / 112500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-17684247417917 / 150000000000000000 : ℚ),
    (44459472272677 / 600000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_18_0_correct (a b : Fin 4) :
    correctionCellCoefficient 18 0 a b = cellMatrix_18_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 18 0 a.val b.val = cellMatrix_18_0 a b) a b

end PartialBalayage.Maximal.Square
