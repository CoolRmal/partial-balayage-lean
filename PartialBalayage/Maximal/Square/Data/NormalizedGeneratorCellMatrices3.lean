/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.ExactRationalLiteral
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix12
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix13
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix14
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix15

/-!
# Normalized exact generator-cell coefficient cache

Each directly reduced rational is checked by Lean's ordinary kernel, and the
whole finite table is identified with the already proved actual coefficients.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Directly reduced exact coefficient rows for actual generator cell 12. -/
def normalizedGeneratorCellMatrix12 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral (-529492956971297) 150000000000000000),
    (exactRationalLiteral 529492956971297 50000000000000000),
    (exactRationalLiteral (-529492956971297) 50000000000000000),
    (exactRationalLiteral 529492956971297 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-13862353202520581) 75000000000000000),
    (exactRationalLiteral 67990523442507 12500000000000000),
    (exactRationalLiteral 13454410061865539 50000000000000000),
    (exactRationalLiteral (-2709012818624443) 20000000000000000)
  ],
  ![
    (exactRationalLiteral 30873866603322537 50000000000000000),
    (exactRationalLiteral 6570655834553467 50000000000000000),
    (exactRationalLiteral (-57755262527727897) 50000000000000000),
    (exactRationalLiteral 27959019610428803 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-56346410604862721) 100000000000000000),
    (exactRationalLiteral (-72787107635935297) 100000000000000000),
    (exactRationalLiteral 212072807683982373 100000000000000000),
    (exactRationalLiteral (-71289140761686043) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-2491196311531681) 75000000000000000),
    (exactRationalLiteral 57048290513515489 50000000000000000),
    (exactRationalLiteral (-97316391892012589) 50000000000000000),
    (exactRationalLiteral 237957605858757751 300000000000000000)
  ],
  ![
    (exactRationalLiteral 14692898845080211 75000000000000000),
    (exactRationalLiteral (-6865797019560851) 10000000000000000),
    (exactRationalLiteral 21334901054147737 25000000000000000),
    (exactRationalLiteral (-2900093735405503) 9375000000000000)
  ],
  ![
    (exactRationalLiteral (-481004909371369) 37500000000000000),
    (exactRationalLiteral 672765262629283 6250000000000000),
    (exactRationalLiteral (-5844936262272709) 50000000000000000),
    (exactRationalLiteral 4839691415139439 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-71907945385531) 7500000000000000),
    (exactRationalLiteral 324490514236843 25000000000000000),
    (exactRationalLiteral (-704063576347703) 50000000000000000),
    (exactRationalLiteral 2530097051616721 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-315527797614799) 75000000000000000),
    (exactRationalLiteral 185378568013201 50000000000000000),
    (exactRationalLiteral 43980474197659 50000000000000000),
    (exactRationalLiteral (-544978655026261) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 2074565405797 4000000000000000),
    (exactRationalLiteral 74132250713823 100000000000000000),
    (exactRationalLiteral (-128201243212437) 100000000000000000),
    (exactRationalLiteral 79305282205247 100000000000000000)
  ],
  ![
    (exactRationalLiteral 1807523260342609 300000000000000000),
    (exactRationalLiteral (-129747349707627) 100000000000000000),
    (exactRationalLiteral 54737195362219 100000000000000000),
    (exactRationalLiteral (-17346480464599) 60000000000000000)
  ],
  ![
    (exactRationalLiteral (-390596859810403) 300000000000000000),
    (exactRationalLiteral 58828156917469 100000000000000000),
    (exactRationalLiteral 11668430436371 100000000000000000),
    (exactRationalLiteral (-8694142937361) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-56330102757031) 15000000000000000),
    (exactRationalLiteral 8210334021307 5000000000000000),
    (exactRationalLiteral (-40276286295907) 50000000000000000),
    (exactRationalLiteral 19290239901107 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-2784144496611) 4000000000000000),
    (exactRationalLiteral 22321858252629 100000000000000000),
    (exactRationalLiteral 9553746409113 20000000000000000),
    (exactRationalLiteral (-72143157584399) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-5461363015783409) 300000000000000000),
    (exactRationalLiteral 617644362770451 100000000000000000),
    (exactRationalLiteral (-172325528619779) 100000000000000000),
    (exactRationalLiteral 117210238081823 300000000000000000)
  ],
  ![
    (exactRationalLiteral 2354173083769 75000000000000),
    (exactRationalLiteral (-318037160245971) 25000000000000000),
    (exactRationalLiteral 39501611136137 12500000000000000),
    (exactRationalLiteral (-87784858638103) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-5461363015783409) 300000000000000000),
    (exactRationalLiteral 617644362770451 100000000000000000),
    (exactRationalLiteral (-172325528619779) 100000000000000000),
    (exactRationalLiteral 117210238081823 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-2784144496611) 4000000000000000),
    (exactRationalLiteral 22321858252629 100000000000000000),
    (exactRationalLiteral 9553746409113 20000000000000000),
    (exactRationalLiteral (-72143157584399) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-56330102757031) 15000000000000000),
    (exactRationalLiteral 8210334021307 5000000000000000),
    (exactRationalLiteral (-40276286295907) 50000000000000000),
    (exactRationalLiteral 19290239901107 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-390596859810403) 300000000000000000),
    (exactRationalLiteral 58828156917469 100000000000000000),
    (exactRationalLiteral 11668430436371 100000000000000000),
    (exactRationalLiteral (-8694142937361) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 1807523260342609 300000000000000000),
    (exactRationalLiteral (-129747349707627) 100000000000000000),
    (exactRationalLiteral 54737195362219 100000000000000000),
    (exactRationalLiteral (-17346480464599) 60000000000000000)
  ],
  ![
    (exactRationalLiteral 2074565405797 4000000000000000),
    (exactRationalLiteral 74132250713823 100000000000000000),
    (exactRationalLiteral (-128201243212437) 100000000000000000),
    (exactRationalLiteral 79305282205247 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-315527797614799) 75000000000000000),
    (exactRationalLiteral 185378568013201 50000000000000000),
    (exactRationalLiteral 43980474197659 50000000000000000),
    (exactRationalLiteral (-544978655026261) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-71907945385531) 7500000000000000),
    (exactRationalLiteral 324490514236843 25000000000000000),
    (exactRationalLiteral (-704063576347703) 50000000000000000),
    (exactRationalLiteral 2530097051616721 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-481004909371369) 37500000000000000),
    (exactRationalLiteral 672765262629283 6250000000000000),
    (exactRationalLiteral (-5844936262272709) 50000000000000000),
    (exactRationalLiteral 4839691415139439 150000000000000000)
  ],
  ![
    (exactRationalLiteral 14692898845080211 75000000000000000),
    (exactRationalLiteral (-6865797019560851) 10000000000000000),
    (exactRationalLiteral 21334901054147737 25000000000000000),
    (exactRationalLiteral (-2900093735405503) 9375000000000000)
  ],
  ![
    (exactRationalLiteral (-2491196311531681) 75000000000000000),
    (exactRationalLiteral 57048290513515489 50000000000000000),
    (exactRationalLiteral (-97316391892012589) 50000000000000000),
    (exactRationalLiteral 237957605858757751 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-56346410604862721) 100000000000000000),
    (exactRationalLiteral (-72787107635935297) 100000000000000000),
    (exactRationalLiteral 212072807683982373 100000000000000000),
    (exactRationalLiteral (-71289140761686043) 75000000000000000)
  ],
  ![
    (exactRationalLiteral 30873866603322537 50000000000000000),
    (exactRationalLiteral 6570655834553467 50000000000000000),
    (exactRationalLiteral (-57755262527727897) 50000000000000000),
    (exactRationalLiteral 27959019610428803 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-13862353202520581) 75000000000000000),
    (exactRationalLiteral 67990523442507 12500000000000000),
    (exactRationalLiteral 13454410061865539 50000000000000000),
    (exactRationalLiteral (-2709012818624443) 20000000000000000)
  ],
  ![
    (exactRationalLiteral (-529492956971297) 150000000000000000),
    (exactRationalLiteral 529492956971297 50000000000000000),
    (exactRationalLiteral (-529492956971297) 50000000000000000),
    (exactRationalLiteral 529492956971297 150000000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix12_eq :
    normalizedGeneratorCellMatrix12 = generatorCellMatrix12 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix12 j a = generatorCellMatrix12 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 13. -/
def normalizedGeneratorCellMatrix13 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral (-13726372155635567) 300000000000000000),
    (exactRationalLiteral 13726372155635567 100000000000000000),
    (exactRationalLiteral (-13726372155635567) 100000000000000000),
    (exactRationalLiteral 13726372155635567 300000000000000000)
  ],
  ![
    (exactRationalLiteral 764827952057691 5000000000000000),
    (exactRationalLiteral (-12531405194807959) 25000000000000000),
    (exactRationalLiteral 1632612268972407 3125000000000000),
    (exactRationalLiteral (-26651289260529809) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-36338694717191107) 300000000000000000),
    (exactRationalLiteral 66201944685285277 100000000000000000),
    (exactRationalLiteral (-73083755362761799) 100000000000000000),
    (exactRationalLiteral 73841389265976539 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-4538595886117191) 100000000000000000),
    (exactRationalLiteral (-37211380682261627) 100000000000000000),
    (exactRationalLiteral 43324822074732573 100000000000000000),
    (exactRationalLiteral (-18191527583991313) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 8006748955146031 150000000000000000),
    (exactRationalLiteral 921823870459729 10000000000000000),
    (exactRationalLiteral (-1865848829096287) 25000000000000000),
    (exactRationalLiteral (-931638595014047) 37500000000000000)
  ],
  ![
    (exactRationalLiteral 127269107828219 12500000000000000),
    (exactRationalLiteral (-293611801674343) 10000000000000000),
    (exactRationalLiteral (-100524484713327) 5000000000000000),
    (exactRationalLiteral 858664514355649 18750000000000000)
  ],
  ![
    (exactRationalLiteral (-225572017016207) 100000000000000000),
    (exactRationalLiteral 1011804803173281 100000000000000000),
    (exactRationalLiteral 224393979784263 20000000000000000),
    (exactRationalLiteral (-1767455142731489) 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-430935592220297) 300000000000000000),
    (exactRationalLiteral 1700377790777 100000000000000000),
    (exactRationalLiteral (-457017706630943) 100000000000000000),
    (exactRationalLiteral 728088906500489 150000000000000000)
  ],
  ![
    (exactRationalLiteral 38550212425779 50000000000000000),
    (exactRationalLiteral 5564561090469 10000000000000000),
    (exactRationalLiteral 13714325425413 12500000000000000),
    (exactRationalLiteral (-427624316285813) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 149576039498339 30000000000000000),
    (exactRationalLiteral (-13375670163273) 12500000000000000),
    (exactRationalLiteral (-3999400870097) 12500000000000000),
    (exactRationalLiteral 2570311595459 6250000000000000)
  ],
  ![
    (exactRationalLiteral (-102594763280483) 150000000000000000),
    (exactRationalLiteral 3505161811133 6250000000000000),
    (exactRationalLiteral (-450437449241) 3125000000000000),
    (exactRationalLiteral (-1084400499207) 20000000000000000)
  ],
  ![
    (exactRationalLiteral (-133079795338869) 50000000000000000),
    (exactRationalLiteral 4013124742347 5000000000000000),
    (exactRationalLiteral (-1695806493693) 50000000000000000),
    (exactRationalLiteral (-589013625473) 18750000000000000)
  ],
  ![
    (exactRationalLiteral (-35341111967821) 150000000000000000),
    (exactRationalLiteral 142863014873 312500000000000),
    (exactRationalLiteral (-12187212769417) 50000000000000000),
    (exactRationalLiteral 8354798986359 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-133606542508319) 10000000000000000),
    (exactRationalLiteral 97550885903179 25000000000000000),
    (exactRationalLiteral (-13778822634489) 25000000000000000),
    (exactRationalLiteral (-4146740362573) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 637271536211543 30000000000000000),
    (exactRationalLiteral (-407846290040949) 50000000000000000),
    (exactRationalLiteral 14044317181289 10000000000000000),
    (exactRationalLiteral (-4147458994429) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-133606542508319) 10000000000000000),
    (exactRationalLiteral 97550885903179 25000000000000000),
    (exactRationalLiteral (-13778822634489) 25000000000000000),
    (exactRationalLiteral (-4146740362573) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-35341111967821) 150000000000000000),
    (exactRationalLiteral 142863014873 312500000000000),
    (exactRationalLiteral (-12187212769417) 50000000000000000),
    (exactRationalLiteral 8354798986359 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-133079795338869) 50000000000000000),
    (exactRationalLiteral 4013124742347 5000000000000000),
    (exactRationalLiteral (-1695806493693) 50000000000000000),
    (exactRationalLiteral (-589013625473) 18750000000000000)
  ],
  ![
    (exactRationalLiteral (-102594763280483) 150000000000000000),
    (exactRationalLiteral 3505161811133 6250000000000000),
    (exactRationalLiteral (-450437449241) 3125000000000000),
    (exactRationalLiteral (-1084400499207) 20000000000000000)
  ],
  ![
    (exactRationalLiteral 149576039498339 30000000000000000),
    (exactRationalLiteral (-13375670163273) 12500000000000000),
    (exactRationalLiteral (-3999400870097) 12500000000000000),
    (exactRationalLiteral 2570311595459 6250000000000000)
  ],
  ![
    (exactRationalLiteral 38550212425779 50000000000000000),
    (exactRationalLiteral 5564561090469 10000000000000000),
    (exactRationalLiteral 13714325425413 12500000000000000),
    (exactRationalLiteral (-427624316285813) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-430935592220297) 300000000000000000),
    (exactRationalLiteral 1700377790777 100000000000000000),
    (exactRationalLiteral (-457017706630943) 100000000000000000),
    (exactRationalLiteral 728088906500489 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-225572017016207) 100000000000000000),
    (exactRationalLiteral 1011804803173281 100000000000000000),
    (exactRationalLiteral 224393979784263 20000000000000000),
    (exactRationalLiteral (-1767455142731489) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 127269107828219 12500000000000000),
    (exactRationalLiteral (-293611801674343) 10000000000000000),
    (exactRationalLiteral (-100524484713327) 5000000000000000),
    (exactRationalLiteral 858664514355649 18750000000000000)
  ],
  ![
    (exactRationalLiteral 8006748955146031 150000000000000000),
    (exactRationalLiteral 921823870459729 10000000000000000),
    (exactRationalLiteral (-1865848829096287) 25000000000000000),
    (exactRationalLiteral (-931638595014047) 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-4538595886117191) 100000000000000000),
    (exactRationalLiteral (-37211380682261627) 100000000000000000),
    (exactRationalLiteral 43324822074732573 100000000000000000),
    (exactRationalLiteral (-18191527583991313) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-36338694717191107) 300000000000000000),
    (exactRationalLiteral 66201944685285277 100000000000000000),
    (exactRationalLiteral (-73083755362761799) 100000000000000000),
    (exactRationalLiteral 73841389265976539 300000000000000000)
  ],
  ![
    (exactRationalLiteral 764827952057691 5000000000000000),
    (exactRationalLiteral (-12531405194807959) 25000000000000000),
    (exactRationalLiteral 1632612268972407 3125000000000000),
    (exactRationalLiteral (-26651289260529809) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-13726372155635567) 300000000000000000),
    (exactRationalLiteral 13726372155635567 100000000000000000),
    (exactRationalLiteral (-13726372155635567) 100000000000000000),
    (exactRationalLiteral 13726372155635567 300000000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix13_eq :
    normalizedGeneratorCellMatrix13 = generatorCellMatrix13 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix13 j a = generatorCellMatrix13 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 14. -/
def normalizedGeneratorCellMatrix14 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral (-529492956971297) 150000000000000000),
    (exactRationalLiteral 529492956971297 50000000000000000),
    (exactRationalLiteral (-529492956971297) 50000000000000000),
    (exactRationalLiteral 529492956971297 150000000000000000)
  ],
  ![
    (exactRationalLiteral 8428631258177933 150000000000000000),
    (exactRationalLiteral (-3062088387130891) 50000000000000000),
    (exactRationalLiteral 37881695160737 5000000000000000),
    (exactRationalLiteral 1925637532308781 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-31658518648921361) 300000000000000000),
    (exactRationalLiteral 13055208299220893 100000000000000000),
    (exactRationalLiteral 6941766906749947 100000000000000000),
    (exactRationalLiteral (-20505361186775569) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 864057457176007 18750000000000000),
    (exactRationalLiteral (-6580830344142691) 50000000000000000),
    (exactRationalLiteral (-3729126019124381) 25000000000000000),
    (exactRationalLiteral 218662451568751 1562500000000000)
  ],
  ![
    (exactRationalLiteral 195326768453773 30000000000000000),
    (exactRationalLiteral 3390767412206937 50000000000000000),
    (exactRationalLiteral 2932035633855961 25000000000000000),
    (exactRationalLiteral (-38582930800959367) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1407475423469 1000000000000000),
    (exactRationalLiteral (-511655206794639) 25000000000000000),
    (exactRationalLiteral (-65318680144893) 1562500000000000),
    (exactRationalLiteral 1796257059135139 30000000000000000)
  ],
  ![
    (exactRationalLiteral (-340709765739817) 300000000000000000),
    (exactRationalLiteral 543842777529869 100000000000000000),
    (exactRationalLiteral 199832021274007 20000000000000000),
    (exactRationalLiteral (-4754863242510373) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 299757601192843 300000000000000000),
    (exactRationalLiteral (-30509899714903) 20000000000000000),
    (exactRationalLiteral (-317909712882509) 100000000000000000),
    (exactRationalLiteral 389406795475869 100000000000000000)
  ],
  ![
    (exactRationalLiteral 601066823382271 150000000000000000),
    (exactRationalLiteral (-5952602330713) 12500000000000000),
    (exactRationalLiteral 11422468702657 12500000000000000),
    (exactRationalLiteral (-161255903167919) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-96449762241823) 300000000000000000),
    (exactRationalLiteral 10988584738599 100000000000000000),
    (exactRationalLiteral (-30680005863817) 100000000000000000),
    (exactRationalLiteral 81269273124701 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-14432258611553) 7500000000000000),
    (exactRationalLiteral 320275254323 500000000000000),
    (exactRationalLiteral (-6407915497477) 50000000000000000),
    (exactRationalLiteral (-3930152705973) 50000000000000000)
  ],
  ![
    (exactRationalLiteral 18407390685013 300000000000000000),
    (exactRationalLiteral 22031710640769 100000000000000000),
    (exactRationalLiteral 689971420243 100000000000000000),
    (exactRationalLiteral 30244584826067 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-752806249187609) 75000000000000000),
    (exactRationalLiteral 135839740905829 50000000000000000),
    (exactRationalLiteral (-31704385631551) 50000000000000000),
    (exactRationalLiteral (-10603976961667) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 433037730133069 30000000000000000),
    (exactRationalLiteral (-275698036216917) 50000000000000000),
    (exactRationalLiteral 61926667917587 50000000000000000),
    (exactRationalLiteral 1823483420109 25000000000000000)
  ],
  ![
    (exactRationalLiteral (-752806249187609) 75000000000000000),
    (exactRationalLiteral 135839740905829 50000000000000000),
    (exactRationalLiteral (-31704385631551) 50000000000000000),
    (exactRationalLiteral (-10603976961667) 100000000000000000)
  ],
  ![
    (exactRationalLiteral 18407390685013 300000000000000000),
    (exactRationalLiteral 22031710640769 100000000000000000),
    (exactRationalLiteral 689971420243 100000000000000000),
    (exactRationalLiteral 30244584826067 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-14432258611553) 7500000000000000),
    (exactRationalLiteral 320275254323 500000000000000),
    (exactRationalLiteral (-6407915497477) 50000000000000000),
    (exactRationalLiteral (-3930152705973) 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-96449762241823) 300000000000000000),
    (exactRationalLiteral 10988584738599 100000000000000000),
    (exactRationalLiteral (-30680005863817) 100000000000000000),
    (exactRationalLiteral 81269273124701 300000000000000000)
  ],
  ![
    (exactRationalLiteral 601066823382271 150000000000000000),
    (exactRationalLiteral (-5952602330713) 12500000000000000),
    (exactRationalLiteral 11422468702657 12500000000000000),
    (exactRationalLiteral (-161255903167919) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 299757601192843 300000000000000000),
    (exactRationalLiteral (-30509899714903) 20000000000000000),
    (exactRationalLiteral (-317909712882509) 100000000000000000),
    (exactRationalLiteral 389406795475869 100000000000000000)
  ],
  ![
    (exactRationalLiteral (-340709765739817) 300000000000000000),
    (exactRationalLiteral 543842777529869 100000000000000000),
    (exactRationalLiteral 199832021274007 20000000000000000),
    (exactRationalLiteral (-4754863242510373) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1407475423469 1000000000000000),
    (exactRationalLiteral (-511655206794639) 25000000000000000),
    (exactRationalLiteral (-65318680144893) 1562500000000000),
    (exactRationalLiteral 1796257059135139 30000000000000000)
  ],
  ![
    (exactRationalLiteral 195326768453773 30000000000000000),
    (exactRationalLiteral 3390767412206937 50000000000000000),
    (exactRationalLiteral 2932035633855961 25000000000000000),
    (exactRationalLiteral (-38582930800959367) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 864057457176007 18750000000000000),
    (exactRationalLiteral (-6580830344142691) 50000000000000000),
    (exactRationalLiteral (-3729126019124381) 25000000000000000),
    (exactRationalLiteral 218662451568751 1562500000000000)
  ],
  ![
    (exactRationalLiteral (-31658518648921361) 300000000000000000),
    (exactRationalLiteral 13055208299220893 100000000000000000),
    (exactRationalLiteral 6941766906749947 100000000000000000),
    (exactRationalLiteral (-20505361186775569) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 8428631258177933 150000000000000000),
    (exactRationalLiteral (-3062088387130891) 50000000000000000),
    (exactRationalLiteral 37881695160737 5000000000000000),
    (exactRationalLiteral 1925637532308781 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-529492956971297) 150000000000000000),
    (exactRationalLiteral 529492956971297 50000000000000000),
    (exactRationalLiteral (-529492956971297) 50000000000000000),
    (exactRationalLiteral 529492956971297 150000000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix14_eq :
    normalizedGeneratorCellMatrix14 = generatorCellMatrix14 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix14 j a = generatorCellMatrix14 j a := by
    decide +kernel
  exact h k b

/-- Directly reduced exact coefficient rows for actual generator cell 15. -/
def normalizedGeneratorCellMatrix15 : Fin 53 → Fin 4 → ℚ := ![
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (exactRationalLiteral 2683271435523521 300000000000000000),
    (exactRationalLiteral (-2683271435523521) 100000000000000000),
    (exactRationalLiteral 2683271435523521 100000000000000000),
    (exactRationalLiteral (-2683271435523521) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 260901526073853 10000000000000000),
    (exactRationalLiteral 3216690462972609 50000000000000000),
    (exactRationalLiteral (-6781797140012811) 50000000000000000),
    (exactRationalLiteral 178423968302769 3125000000000000)
  ],
  ![
    (exactRationalLiteral (-14213192139166207) 150000000000000000),
    (exactRationalLiteral (-505739070040119) 50000000000000000),
    (exactRationalLiteral 6766671656175667 25000000000000000),
    (exactRationalLiteral (-43873049958819251) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 6299789654363839 100000000000000000),
    (exactRationalLiteral (-1669022181139561) 20000000000000000),
    (exactRationalLiteral (-26854788265535523) 100000000000000000),
    (exactRationalLiteral 7274165131148737 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-148117925481517) 150000000000000000),
    (exactRationalLiteral 755515870562653 10000000000000000),
    (exactRationalLiteral 6891087531039119 50000000000000000),
    (exactRationalLiteral (-42834549095076847) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-233282178275239) 150000000000000000),
    (exactRationalLiteral (-1106350126120217) 50000000000000000),
    (exactRationalLiteral (-1877851568070169) 50000000000000000),
    (exactRationalLiteral 17656141561342373 300000000000000000)
  ],
  ![
    (exactRationalLiteral 28300176624689 150000000000000000),
    (exactRationalLiteral 189925731044037 50000000000000000),
    (exactRationalLiteral 425155336772549 50000000000000000),
    (exactRationalLiteral (-437334829240013) 30000000000000000)
  ],
  ![
    (exactRationalLiteral 6318116458471 1875000000000000),
    (exactRationalLiteral (-18737312573903) 10000000000000000),
    (exactRationalLiteral (-115566028357291) 50000000000000000),
    (exactRationalLiteral 490433089835143 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-9281844061597) 37500000000000000),
    (exactRationalLiteral 15448923067833 50000000000000000),
    (exactRationalLiteral 12647316815221 25000000000000000),
    (exactRationalLiteral (-123505652760343) 150000000000000000)
  ],
  ![
    (exactRationalLiteral (-22357680054451) 15000000000000000),
    (exactRationalLiteral 7421236319427 50000000000000000),
    (exactRationalLiteral (-4549593403849) 12500000000000000),
    (exactRationalLiteral 15937942064843 50000000000000000)
  ],
  ![
    (exactRationalLiteral 9734751807843 25000000000000000),
    (exactRationalLiteral 26828119153661 50000000000000000),
    (exactRationalLiteral 3093455624631 10000000000000000),
    (exactRationalLiteral (-122622094893391) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-2418224795989769) 300000000000000000),
    (exactRationalLiteral 113050008400453 100000000000000000),
    (exactRationalLiteral (-95220702148103) 100000000000000000),
    (exactRationalLiteral 225371818158323 300000000000000000)
  ],
  ![
    (exactRationalLiteral 1534815446288009 150000000000000000),
    (exactRationalLiteral (-140903799861089) 50000000000000000),
    (exactRationalLiteral 72867568438241 50000000000000000),
    (exactRationalLiteral (-73088517790967) 75000000000000000)
  ],
  ![
    (exactRationalLiteral (-2418224795989769) 300000000000000000),
    (exactRationalLiteral 113050008400453 100000000000000000),
    (exactRationalLiteral (-95220702148103) 100000000000000000),
    (exactRationalLiteral 225371818158323 300000000000000000)
  ],
  ![
    (exactRationalLiteral 9734751807843 25000000000000000),
    (exactRationalLiteral 26828119153661 50000000000000000),
    (exactRationalLiteral 3093455624631 10000000000000000),
    (exactRationalLiteral (-122622094893391) 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-22357680054451) 15000000000000000),
    (exactRationalLiteral 7421236319427 50000000000000000),
    (exactRationalLiteral (-4549593403849) 12500000000000000),
    (exactRationalLiteral 15937942064843 50000000000000000)
  ],
  ![
    (exactRationalLiteral (-9281844061597) 37500000000000000),
    (exactRationalLiteral 15448923067833 50000000000000000),
    (exactRationalLiteral 12647316815221 25000000000000000),
    (exactRationalLiteral (-123505652760343) 150000000000000000)
  ],
  ![
    (exactRationalLiteral 6318116458471 1875000000000000),
    (exactRationalLiteral (-18737312573903) 10000000000000000),
    (exactRationalLiteral (-115566028357291) 50000000000000000),
    (exactRationalLiteral 490433089835143 150000000000000000)
  ],
  ![
    (exactRationalLiteral 28300176624689 150000000000000000),
    (exactRationalLiteral 189925731044037 50000000000000000),
    (exactRationalLiteral 425155336772549 50000000000000000),
    (exactRationalLiteral (-437334829240013) 30000000000000000)
  ],
  ![
    (exactRationalLiteral (-233282178275239) 150000000000000000),
    (exactRationalLiteral (-1106350126120217) 50000000000000000),
    (exactRationalLiteral (-1877851568070169) 50000000000000000),
    (exactRationalLiteral 17656141561342373 300000000000000000)
  ],
  ![
    (exactRationalLiteral (-148117925481517) 150000000000000000),
    (exactRationalLiteral 755515870562653 10000000000000000),
    (exactRationalLiteral 6891087531039119 50000000000000000),
    (exactRationalLiteral (-42834549095076847) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 6299789654363839 100000000000000000),
    (exactRationalLiteral (-1669022181139561) 20000000000000000),
    (exactRationalLiteral (-26854788265535523) 100000000000000000),
    (exactRationalLiteral 7274165131148737 37500000000000000)
  ],
  ![
    (exactRationalLiteral (-14213192139166207) 150000000000000000),
    (exactRationalLiteral (-505739070040119) 50000000000000000),
    (exactRationalLiteral 6766671656175667 25000000000000000),
    (exactRationalLiteral (-43873049958819251) 300000000000000000)
  ],
  ![
    (exactRationalLiteral 260901526073853 10000000000000000),
    (exactRationalLiteral 3216690462972609 50000000000000000),
    (exactRationalLiteral (-6781797140012811) 50000000000000000),
    (exactRationalLiteral 178423968302769 3125000000000000)
  ],
  ![
    (exactRationalLiteral 2683271435523521 300000000000000000),
    (exactRationalLiteral (-2683271435523521) 100000000000000000),
    (exactRationalLiteral 2683271435523521 100000000000000000),
    (exactRationalLiteral (-2683271435523521) 300000000000000000)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ],
  ![
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (0 : ℚ)
  ]
]

/-- Every normalized coefficient is the original exact checked coefficient. -/
theorem normalizedGeneratorCellMatrix15_eq :
    normalizedGeneratorCellMatrix15 = generatorCellMatrix15 := by
  funext k b
  have h : ∀ j : Fin 53, ∀ a : Fin 4,
      normalizedGeneratorCellMatrix15 j a = generatorCellMatrix15 j a := by
    decide +kernel
  exact h k b

end PartialBalayage.Maximal.Square
