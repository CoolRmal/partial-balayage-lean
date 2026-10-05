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

/-- Candidate finite rational coefficient matrix on cell (8, 0). -/
def cellMatrix_8_0 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-22472627720058199 / 180000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-8857112328360569 / 300000000000000000 : ℚ),
    (26104258996393151 / 1800000000000000000 : ℚ)
  ],
  ![
    (30858490915827529 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (1663230876727027 / 100000000000000000 : ℚ),
    (-278646842228033 / 40000000000000000 : ℚ)
  ],
  ![
    (-6360833697637787 / 300000000000000000 : ℚ),
    (0 / 1 : ℚ),
    (-486110499259307 / 100000000000000000 : ℚ),
    (1153766953128797 / 600000000000000000 : ℚ)
  ],
  ![
    (277433911427081 / 112500000000000000 : ℚ),
    (0 / 1 : ℚ),
    (245147778336601 / 300000000000000000 : ℚ),
    (-65433731108839 / 200000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_0_correct (a b : Fin 4) :
    correctionCellCoefficient 8 0 a b = cellMatrix_8_0 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 0 a.val b.val = cellMatrix_8_0 a b) a b

/-- Candidate finite rational coefficient matrix on cell (8, 1). -/
def cellMatrix_8_1 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-251764692174352253 / 1800000000000000000 : ℚ),
    (-24864507512131 / 1600000000000000 : ℚ),
    (8390034339672013 / 600000000000000000 : ℚ),
    (593317486706089 / 900000000000000000 : ℚ)
  ],
  ![
    (2700666578343869 / 24000000000000000 : ℚ),
    (2473220873487613 / 200000000000000000 : ℚ),
    (-853240879966441 / 200000000000000000 : ℚ),
    (-40728345657323 / 60000000000000000 : ℚ)
  ],
  ![
    (-14484563437702619 / 600000000000000000 : ℚ),
    (-790675043908431 / 200000000000000000 : ℚ),
    (181545954610183 / 200000000000000000 : ℚ),
    (3900219692971 / 30000000000000000 : ℚ)
  ],
  ![
    (5320925672873351 / 1800000000000000000 : ℚ),
    (391687533366853 / 600000000000000000 : ℚ),
    (-98608023306349 / 600000000000000000 : ℚ),
    (10646895253067 / 900000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_1_correct (a b : Fin 4) :
    correctionCellCoefficient 8 1 a b = cellMatrix_8_1 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 1 a.val b.val = cellMatrix_8_1 a b) a b

/-- Candidate finite rational coefficient matrix on cell (8, 2). -/
def cellMatrix_8_2 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-28153391681452379 / 200000000000000000 : ℚ),
    (8642513335707079 / 600000000000000000 : ℚ),
    (3192223104361397 / 200000000000000000 : ℚ),
    (-65189007018877 / 450000000000000000 : ℚ)
  ],
  ![
    (23989773660862337 / 200000000000000000 : ℚ),
    (359455656981501 / 200000000000000000 : ℚ),
    (-1260524336539671 / 200000000000000000 : ℚ),
    (-10326295616309 / 25000000000000000 : ℚ)
  ],
  ![
    (-5411315437245981 / 200000000000000000 : ℚ),
    (-69915748165729 / 40000000000000000 : ℚ),
    (259550348469603 / 200000000000000000 : ℚ),
    (4442157941377 / 18750000000000000 : ℚ)
  ],
  ![
    (2073819331186999 / 600000000000000000 : ℚ),
    (71921759086763 / 200000000000000000 : ℚ),
    (-5154282186681 / 40000000000000000 : ℚ),
    (-141765708943379 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_2_correct (a b : Fin 4) :
    correctionCellCoefficient 8 2 a b = cellMatrix_8_2 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 2 a.val b.val = cellMatrix_8_2 a b) a b

/-- Candidate finite rational coefficient matrix on cell (8, 3). -/
def cellMatrix_8_3 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-198983733214773109 / 1800000000000000000 : ℚ),
    (9178365311266651 / 200000000000000000 : ℚ),
    (9315913285008683 / 600000000000000000 : ℚ),
    (-2606709954620969 / 900000000000000000 : ℚ)
  ],
  ![
    (4601218923274739 / 40000000000000000 : ℚ),
    (-2409424110889257 / 200000000000000000 : ℚ),
    (-1508355431331087 / 200000000000000000 : ℚ),
    (93344494106059 / 150000000000000000 : ℚ)
  ],
  ![
    (-3272376486938201 / 120000000000000000 : ℚ),
    (2493368081877 / 1600000000000000 : ℚ),
    (401699402593667 / 200000000000000000 : ℚ),
    (-2908178358757 / 60000000000000000 : ℚ)
  ],
  ![
    (81188067724973 / 22500000000000000 : ℚ),
    (-251965304011 / 1875000000000000 : ℚ),
    (-109539970871797 / 300000000000000000 : ℚ),
    (1570904284721 / 150000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_3_correct (a b : Fin 4) :
    correctionCellCoefficient 8 3 a b = cellMatrix_8_3 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 3 a.val b.val = cellMatrix_8_3 a b) a b

/-- Candidate finite rational coefficient matrix on cell (8, 4). -/
def cellMatrix_8_4 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (-93644125467589139 / 1800000000000000000 : ℚ),
    (13651167531525127 / 200000000000000000 : ℚ),
    (820498675153349 / 120000000000000000 : ℚ),
    (-4877842392635717 / 900000000000000000 : ℚ)
  ],
  ![
    (57638323198884289 / 600000000000000000 : ℚ),
    (-1010551399425439 / 40000000000000000 : ℚ),
    (-1134977454906851 / 200000000000000000 : ℚ),
    (137070048624299 / 50000000000000000 : ℚ)
  ],
  ![
    (-14250852979793699 / 600000000000000000 : ℚ),
    (1085988031834389 / 200000000000000000 : ℚ),
    (372617619006097 / 200000000000000000 : ℚ),
    (-72659823945869 / 75000000000000000 : ℚ)
  ],
  ![
    (112295395046663 / 36000000000000000 : ℚ),
    (-20830747056419 / 25000000000000000 : ℚ),
    (-100114545163471 / 300000000000000000 : ℚ),
    (9025871386889 / 50000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_4_correct (a b : Fin 4) :
    correctionCellCoefficient 8 4 a b = cellMatrix_8_4 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 4 a.val b.val = cellMatrix_8_4 a b) a b

/-- Candidate finite rational coefficient matrix on cell (8, 5). -/
def cellMatrix_8_5 : Fin 4 → Fin 4 → ℚ := ![
  ![
    (2117878510544387 / 120000000000000000 : ℚ),
    (39402804560837437 / 600000000000000000 : ℚ),
    (-1884397136501563 / 200000000000000000 : ℚ),
    (-221245573775143 / 300000000000000000 : ℚ)
  ],
  ![
    (40719960426273739 / 600000000000000000 : ℚ),
    (-5677871323449309 / 200000000000000000 : ℚ),
    (509863128584737 / 200000000000000000 : ℚ),
    (15044792458813 / 60000000000000000 : ℚ)
  ],
  ![
    (-3485438206279731 / 200000000000000000 : ℚ),
    (1249944678279631 / 200000000000000000 : ℚ),
    (-41732194512171 / 40000000000000000 : ℚ),
    (-1365345630911 / 10000000000000000 : ℚ)
  ],
  ![
    (47990000790227 / 22500000000000000 : ℚ),
    (-8991636563749 / 9375000000000000 : ℚ),
    (62351139800531 / 300000000000000000 : ℚ),
    (18031486338337 / 1800000000000000000 : ℚ)
  ]
]

/-- All sixteen entries are the actual signed cell coefficients. -/
theorem cellMatrix_8_5_correct (a b : Fin 4) :
    correctionCellCoefficient 8 5 a b = cellMatrix_8_5 a b := by
  rw [correctionCellCoefficient_eq_local_range]
  exact (by decide +kernel : ∀ a b : Fin 4,
    localCellCoefficient 8 5 a.val b.val = cellMatrix_8_5 a b) a b

end PartialBalayage.Maximal.Square
