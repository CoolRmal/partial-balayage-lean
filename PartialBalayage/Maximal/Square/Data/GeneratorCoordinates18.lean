/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorCoordinateData
public import PartialBalayage.Maximal.Square.ExactRationalLiteral

/-!
# Checked actual coordinate intervals and signed power lookup

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual coordinate interval candidates, block 18. -/
def generatorCoordinates18 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 4
        lower := (0 : ℚ)
        width := (1 : ℚ)
        centered := ![
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
            (exactRationalLiteral (684347342461457) 600000000000000000),
            (exactRationalLiteral (-684347342461457) 100000000000000000),
            (exactRationalLiteral (684347342461457) 50000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (4200852547840459) 160000000000000000),
            (exactRationalLiteral (-1621792996893381) 80000000000000000),
            (exactRationalLiteral (-2038461885315951) 40000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-12342573336230231) 300000000000000000),
            (exactRationalLiteral (25258792051272463) 200000000000000000),
            (exactRationalLiteral (662207462754863) 12500000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-24677644779696197) 1200000000000000000),
            (exactRationalLiteral (-8962306797275621) 50000000000000000),
            (exactRationalLiteral (396204264334787) 20000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (14621126057379097) 300000000000000000),
            (exactRationalLiteral (739774219794977) 8000000000000000),
            (exactRationalLiteral (-114461591004599) 1562500000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6148152533788001) 400000000000000000),
            (exactRationalLiteral (-2381533359793027) 200000000000000000),
            (exactRationalLiteral (983452141470609) 20000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (201742054918273) 120000000000000000),
            (exactRationalLiteral (30020491458971) 50000000000000000),
            (exactRationalLiteral (-135452408316443) 10000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-3053510986936637) 2400000000000000000),
            (exactRationalLiteral (-54573986082923) 80000000000000000),
            (exactRationalLiteral (563102161175659) 200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-955179647143873) 2400000000000000000),
            (exactRationalLiteral (-21850755147029) 400000000000000000),
            (exactRationalLiteral (-172109629652041) 200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (241005883748557) 2400000000000000000),
            (exactRationalLiteral (73900252396311) 400000000000000000),
            (exactRationalLiteral (2619647668573) 8000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (284888868548251) 150000000000000000),
            (exactRationalLiteral (155593144028627) 200000000000000000),
            (exactRationalLiteral (-1128047403461) 12500000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (260744185621381) 600000000000000000),
            (exactRationalLiteral (208659894613071) 200000000000000000),
            (exactRationalLiteral (28198270635109) 50000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2801629173973907) 300000000000000000),
            (exactRationalLiteral (-27051084667983) 20000000000000000),
            (exactRationalLiteral (-22841508932501) 25000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-11576255425781599) 2400000000000000000),
            (exactRationalLiteral (305602982652541) 400000000000000000),
            (exactRationalLiteral (73994982048329) 200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7655920458624313) 2400000000000000000),
            (exactRationalLiteral (352977240704651) 80000000000000000),
            (exactRationalLiteral (56204262334247) 200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12765660046290793) 800000000000000000),
            (exactRationalLiteral (3518953239767963) 400000000000000000),
            (exactRationalLiteral (421355131670037) 200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-43520988689272557) 800000000000000000),
            (exactRationalLiteral (11957240709280477) 400000000000000000),
            (exactRationalLiteral (2393529291726273) 200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-280011105584397367) 1200000000000000000),
            (exactRationalLiteral (89121801727273823) 200000000000000000),
            (exactRationalLiteral (8584915780947521) 100000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (322432271740203703) 200000000000000000),
            (exactRationalLiteral (-84320693871074481) 50000000000000000),
            (exactRationalLiteral (-54556438884588621) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-4843657430883727237) 2400000000000000000),
            (exactRationalLiteral (597740044218109049) 400000000000000000),
            (exactRationalLiteral (582519698331008579) 200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (863601279450205741) 1200000000000000000),
            (exactRationalLiteral (32200358943812989) 200000000000000000),
            (exactRationalLiteral (-325301821061603219) 100000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (46241324356258619) 1200000000000000000),
            (exactRationalLiteral (-68009791145314623) 100000000000000000),
            (exactRationalLiteral (6853654297090019) 4000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-572456680441919787) 800000000000000000),
            (exactRationalLiteral (315357186821635621) 400000000000000000),
            (exactRationalLiteral (-30083020330402917) 40000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (819539810391990553) 600000000000000000),
            (exactRationalLiteral (-113544383744954191) 100000000000000000),
            (exactRationalLiteral (36990921666024373) 50000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-572456680441919787) 800000000000000000),
            (exactRationalLiteral (315357186821635621) 400000000000000000),
            (exactRationalLiteral (-30083020330402917) 40000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (46241324356258619) 1200000000000000000),
            (exactRationalLiteral (-68009791145314623) 100000000000000000),
            (exactRationalLiteral (6853654297090019) 4000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (863601279450205741) 1200000000000000000),
            (exactRationalLiteral (32200358943812989) 200000000000000000),
            (exactRationalLiteral (-325301821061603219) 100000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4843657430883727237) 2400000000000000000),
            (exactRationalLiteral (597740044218109049) 400000000000000000),
            (exactRationalLiteral (582519698331008579) 200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (322432271740203703) 200000000000000000),
            (exactRationalLiteral (-84320693871074481) 50000000000000000),
            (exactRationalLiteral (-54556438884588621) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-280011105584397367) 1200000000000000000),
            (exactRationalLiteral (89121801727273823) 200000000000000000),
            (exactRationalLiteral (8584915780947521) 100000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-43520988689272557) 800000000000000000),
            (exactRationalLiteral (11957240709280477) 400000000000000000),
            (exactRationalLiteral (2393529291726273) 200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12765660046290793) 800000000000000000),
            (exactRationalLiteral (3518953239767963) 400000000000000000),
            (exactRationalLiteral (421355131670037) 200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7655920458624313) 2400000000000000000),
            (exactRationalLiteral (352977240704651) 80000000000000000),
            (exactRationalLiteral (56204262334247) 200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11576255425781599) 2400000000000000000),
            (exactRationalLiteral (305602982652541) 400000000000000000),
            (exactRationalLiteral (73994982048329) 200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2801629173973907) 300000000000000000),
            (exactRationalLiteral (-27051084667983) 20000000000000000),
            (exactRationalLiteral (-22841508932501) 25000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (260744185621381) 600000000000000000),
            (exactRationalLiteral (208659894613071) 200000000000000000),
            (exactRationalLiteral (28198270635109) 50000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (284888868548251) 150000000000000000),
            (exactRationalLiteral (155593144028627) 200000000000000000),
            (exactRationalLiteral (-1128047403461) 12500000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (241005883748557) 2400000000000000000),
            (exactRationalLiteral (73900252396311) 400000000000000000),
            (exactRationalLiteral (2619647668573) 8000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-955179647143873) 2400000000000000000),
            (exactRationalLiteral (-21850755147029) 400000000000000000),
            (exactRationalLiteral (-172109629652041) 200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3053510986936637) 2400000000000000000),
            (exactRationalLiteral (-54573986082923) 80000000000000000),
            (exactRationalLiteral (563102161175659) 200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (201742054918273) 120000000000000000),
            (exactRationalLiteral (30020491458971) 50000000000000000),
            (exactRationalLiteral (-135452408316443) 10000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-6148152533788001) 400000000000000000),
            (exactRationalLiteral (-2381533359793027) 200000000000000000),
            (exactRationalLiteral (983452141470609) 20000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (14621126057379097) 300000000000000000),
            (exactRationalLiteral (739774219794977) 8000000000000000),
            (exactRationalLiteral (-114461591004599) 1562500000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-24677644779696197) 1200000000000000000),
            (exactRationalLiteral (-8962306797275621) 50000000000000000),
            (exactRationalLiteral (396204264334787) 20000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-12342573336230231) 300000000000000000),
            (exactRationalLiteral (25258792051272463) 200000000000000000),
            (exactRationalLiteral (662207462754863) 12500000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (4200852547840459) 160000000000000000),
            (exactRationalLiteral (-1621792996893381) 80000000000000000),
            (exactRationalLiteral (-2038461885315951) 40000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 600000000000000000),
            (exactRationalLiteral (-684347342461457) 100000000000000000),
            (exactRationalLiteral (684347342461457) 50000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (exactRationalLiteral (101673746728037) 2500000000000000),
          (exactRationalLiteral (312230455153523) 3750000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (430518985363777) 5000000000000000),
          (exactRationalLiteral (1053271308509191) 37500000000000000),
          (exactRationalLiteral (345113661525361) 75000000000000000),
          (exactRationalLiteral (75319739950873) 37500000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (328688898274277101) 150000000000000000),
          (exactRationalLiteral (145150688404788731) 50000000000000000),
          (exactRationalLiteral (65673021638309281) 50000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (161918727665951221) 75000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (65673021638309281) 50000000000000000),
          (exactRationalLiteral (145150688404788731) 50000000000000000),
          (exactRationalLiteral (328688898274277101) 150000000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (75319739950873) 37500000000000000),
          (exactRationalLiteral (345113661525361) 75000000000000000),
          (exactRationalLiteral (1053271308509191) 37500000000000000),
          (exactRationalLiteral (430518985363777) 5000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (312230455153523) 3750000000000000),
          (exactRationalLiteral (101673746728037) 2500000000000000),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (46, 26),
      (46, 25),
      (46, 24),
      (46, 23),
      (46, 22),
      (46, 21),
      (46, 20),
      (46, 19),
      (46, 18),
      (46, 17),
      (46, 16),
      (46, 15),
      (46, 14),
      (46, 13),
      (46, 12),
      (46, 11),
      (46, 10),
      (46, 9),
      (46, 8),
      (46, 7),
      (46, 6),
      (46, 5),
      (46, 4),
      (46, 3),
      (46, 2),
      (46, 1),
      (46, 0),
      (45, 63),
      (45, 62),
      (45, 61),
      (45, 60),
      (45, 60),
      (45, 61),
      (45, 62),
      (45, 63),
      (46, 0),
      (46, 1),
      (46, 2),
      (46, 3),
      (46, 4),
      (46, 5),
      (46, 6),
      (46, 7),
      (46, 8),
      (46, 9),
      (46, 10),
      (46, 11),
      (46, 12),
      (46, 13),
      (46, 14),
      (46, 15),
      (46, 16),
      (46, 17)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  },
  {
    cubic :=
      {
        cell := 4
        lower := (0 : ℚ)
        width := (exactRationalLiteral (1) 2)
        centered := ![
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
            (exactRationalLiteral (6159126082153113) 1600000000000000000),
            (exactRationalLiteral (-6159126082153113) 400000000000000000),
            (exactRationalLiteral (2053042027384371) 100000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (34930886317647829) 1280000000000000000),
            (exactRationalLiteral (197008895989707) 12800000000000000),
            (exactRationalLiteral (-7335470616684297) 80000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-129258978522301691) 1920000000000000000),
            (exactRationalLiteral (59857528846039167) 800000000000000000),
            (exactRationalLiteral (30582319954972877) 200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (109362967888198493) 4800000000000000000),
            (exactRationalLiteral (-6269561692889941) 40000000000000000),
            (exactRationalLiteral (-10983858770979493) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (73670223963497773) 3200000000000000000),
            (exactRationalLiteral (84259434338053713) 800000000000000000),
            (exactRationalLiteral (4369071290032659) 200000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-97435126453061467) 9600000000000000000),
            (exactRationalLiteral (-21233746064800251) 800000000000000000),
            (exactRationalLiteral (1873091210922053) 200000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1075128536333423) 1200000000000000000),
            (exactRationalLiteral (967158052444631) 200000000000000000),
            (exactRationalLiteral (-42453511256633) 12500000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-18706016041792723) 19200000000000000000),
            (exactRationalLiteral (-482581617606427) 320000000000000000),
            (exactRationalLiteral (195224044022357) 400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-8150013016499669) 19200000000000000000),
            (exactRationalLiteral (67832524244167) 320000000000000000),
            (exactRationalLiteral (-82346382504869) 400000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1349915052917491) 19200000000000000000),
            (exactRationalLiteral (117912381329127) 1600000000000000000),
            (exactRationalLiteral (46706244827467) 400000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1088294071555303) 640000000000000000),
            (exactRationalLiteral (645682603074127) 800000000000000000),
            (exactRationalLiteral (-5261268504243) 200000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2010583031569337) 9600000000000000000),
            (exactRationalLiteral (604837864008627) 800000000000000000),
            (exactRationalLiteral (117008631903221) 200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-8694269531349133) 960000000000000000),
            (exactRationalLiteral (-364041775847531) 400000000000000000),
            (exactRationalLiteral (-684911054257) 800000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-95708789364054211) 19200000000000000000),
            (exactRationalLiteral (801912060677749) 1600000000000000000),
            (exactRationalLiteral (272509905835757) 400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-27309387192082643) 6400000000000000000),
            (exactRationalLiteral (6674116803735879) 1600000000000000000),
            (exactRationalLiteral (273019485688647) 400000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-345373916103106489) 19200000000000000000),
            (exactRationalLiteral (11689159337323827) 1600000000000000000),
            (exactRationalLiteral (1543943358407951) 400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1170561556431868067) 19200000000000000000),
            (exactRationalLiteral (35186960798535429) 1600000000000000000),
            (exactRationalLiteral (7854943455133933) 400000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1070725148046693807) 3200000000000000000),
            (exactRationalLiteral (276282017208606943) 800000000000000000),
            (exactRationalLiteral (63035358138593307) 200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (4655235795056692489) 2400000000000000000),
            (exactRationalLiteral (-83019711045120413) 100000000000000000),
            (exactRationalLiteral (-116686914509468477) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-41483705917704060787) 19200000000000000000),
            (exactRationalLiteral (-882434486448612343) 1600000000000000000),
            (exactRationalLiteral (2108355266659031381) 400000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4151145224154843973) 9600000000000000000),
            (exactRationalLiteral (369891699554618321) 160000000000000000),
            (exactRationalLiteral (-1070053419874633211) 200000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (33483960540457921) 100000000000000000),
            (exactRationalLiteral (-706845121927178273) 400000000000000000),
            (exactRationalLiteral (131732299959334653) 50000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-18545835953734027847) 19200000000000000000),
            (exactRationalLiteral (1983187925250838821) 1600000000000000000),
            (exactRationalLiteral (-420928974660267167) 400000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2721666904258068159) 1600000000000000000),
            (exactRationalLiteral (-626345316346597779) 400000000000000000),
            (exactRationalLiteral (98185938034732269) 100000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-18545835953734027847) 19200000000000000000),
            (exactRationalLiteral (1983187925250838821) 1600000000000000000),
            (exactRationalLiteral (-420928974660267167) 400000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (33483960540457921) 100000000000000000),
            (exactRationalLiteral (-706845121927178273) 400000000000000000),
            (exactRationalLiteral (131732299959334653) 50000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (4151145224154843973) 9600000000000000000),
            (exactRationalLiteral (369891699554618321) 160000000000000000),
            (exactRationalLiteral (-1070053419874633211) 200000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-41483705917704060787) 19200000000000000000),
            (exactRationalLiteral (-882434486448612343) 1600000000000000000),
            (exactRationalLiteral (2108355266659031381) 400000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4655235795056692489) 2400000000000000000),
            (exactRationalLiteral (-83019711045120413) 100000000000000000),
            (exactRationalLiteral (-116686914509468477) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-1070725148046693807) 3200000000000000000),
            (exactRationalLiteral (276282017208606943) 800000000000000000),
            (exactRationalLiteral (63035358138593307) 200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1170561556431868067) 19200000000000000000),
            (exactRationalLiteral (35186960798535429) 1600000000000000000),
            (exactRationalLiteral (7854943455133933) 400000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-345373916103106489) 19200000000000000000),
            (exactRationalLiteral (11689159337323827) 1600000000000000000),
            (exactRationalLiteral (1543943358407951) 400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-27309387192082643) 6400000000000000000),
            (exactRationalLiteral (6674116803735879) 1600000000000000000),
            (exactRationalLiteral (273019485688647) 400000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-95708789364054211) 19200000000000000000),
            (exactRationalLiteral (801912060677749) 1600000000000000000),
            (exactRationalLiteral (272509905835757) 400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8694269531349133) 960000000000000000),
            (exactRationalLiteral (-364041775847531) 400000000000000000),
            (exactRationalLiteral (-684911054257) 800000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2010583031569337) 9600000000000000000),
            (exactRationalLiteral (604837864008627) 800000000000000000),
            (exactRationalLiteral (117008631903221) 200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1088294071555303) 640000000000000000),
            (exactRationalLiteral (645682603074127) 800000000000000000),
            (exactRationalLiteral (-5261268504243) 200000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1349915052917491) 19200000000000000000),
            (exactRationalLiteral (117912381329127) 1600000000000000000),
            (exactRationalLiteral (46706244827467) 400000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8150013016499669) 19200000000000000000),
            (exactRationalLiteral (67832524244167) 320000000000000000),
            (exactRationalLiteral (-82346382504869) 400000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-18706016041792723) 19200000000000000000),
            (exactRationalLiteral (-482581617606427) 320000000000000000),
            (exactRationalLiteral (195224044022357) 400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1075128536333423) 1200000000000000000),
            (exactRationalLiteral (967158052444631) 200000000000000000),
            (exactRationalLiteral (-42453511256633) 12500000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-97435126453061467) 9600000000000000000),
            (exactRationalLiteral (-21233746064800251) 800000000000000000),
            (exactRationalLiteral (1873091210922053) 200000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (73670223963497773) 3200000000000000000),
            (exactRationalLiteral (84259434338053713) 800000000000000000),
            (exactRationalLiteral (4369071290032659) 200000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (109362967888198493) 4800000000000000000),
            (exactRationalLiteral (-6269561692889941) 40000000000000000),
            (exactRationalLiteral (-10983858770979493) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-129258978522301691) 1920000000000000000),
            (exactRationalLiteral (59857528846039167) 800000000000000000),
            (exactRationalLiteral (30582319954972877) 200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (34930886317647829) 1280000000000000000),
            (exactRationalLiteral (197008895989707) 12800000000000000),
            (exactRationalLiteral (-7335470616684297) 80000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (6159126082153113) 1600000000000000000),
            (exactRationalLiteral (-6159126082153113) 400000000000000000),
            (exactRationalLiteral (2053042027384371) 100000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (exactRationalLiteral (2370725106735793) 80000000000000000),
          (exactRationalLiteral (15765036290904491) 200000000000000000),
          (exactRationalLiteral (5240278380610517) 100000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (71505212116231) 150000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (104168595985026701) 50000000000000000),
          (exactRationalLiteral (454718151749078063) 200000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (161918727665951221) 75000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (454718151749078063) 200000000000000000),
          (exactRationalLiteral (104168595985026701) 50000000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (71505212116231) 150000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (5240278380610517) 100000000000000000),
          (exactRationalLiteral (15765036290904491) 200000000000000000),
          (exactRationalLiteral (2370725106735793) 80000000000000000),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (45, 12),
      (45, 10),
      (45, 8),
      (45, 6),
      (45, 4),
      (45, 2),
      (45, 0),
      (44, 62),
      (44, 60),
      (44, 58),
      (44, 56),
      (44, 54),
      (44, 52),
      (44, 50),
      (44, 48),
      (44, 46),
      (44, 44),
      (44, 42),
      (44, 40),
      (44, 38),
      (44, 36),
      (44, 34),
      (44, 32),
      (44, 30),
      (44, 28),
      (44, 26),
      (44, 24),
      (44, 22),
      (44, 20),
      (44, 18),
      (44, 16),
      (44, 17),
      (44, 19),
      (44, 21),
      (44, 23),
      (44, 25),
      (44, 27),
      (44, 29),
      (44, 31),
      (44, 33),
      (44, 35),
      (44, 37),
      (44, 39),
      (44, 41),
      (44, 43),
      (44, 45),
      (44, 47),
      (44, 49),
      (44, 51),
      (44, 53),
      (44, 55),
      (44, 57),
      (44, 59)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  },
  {
    cubic :=
      {
        cell := 4
        lower := (exactRationalLiteral (1) 2)
        width := (exactRationalLiteral (1) 2)
        centered := ![
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
            (exactRationalLiteral (684347342461457) 4800000000000000000),
            (exactRationalLiteral (-684347342461457) 400000000000000000),
            (exactRationalLiteral (684347342461457) 100000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (24128906906535711) 1280000000000000000),
            (exactRationalLiteral (-11382472682784933) 320000000000000000),
            (exactRationalLiteral (-818376924579507) 80000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-80057884482759481) 9600000000000000000),
            (exactRationalLiteral (102238806462350399) 800000000000000000),
            (exactRationalLiteral (-9391681146817261) 200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-98299332731908153) 1600000000000000000),
            (exactRationalLiteral (-5477153164220367) 40000000000000000),
            (exactRationalLiteral (14945901414327363) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (626834893890236857) 9600000000000000000),
            (exactRationalLiteral (1026203989747961) 32000000000000000),
            (exactRationalLiteral (-33671238587210003) 200000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-138669066680526041) 9600000000000000000),
            (exactRationalLiteral (18104339594024109) 800000000000000000),
            (exactRationalLiteral (17795951618490127) 200000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (19331800776779) 25000000000000000),
            (exactRationalLiteral (-1741890113884229) 200000000000000000),
            (exactRationalLiteral (-592355019068949) 25000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-23392933815085561) 19200000000000000000),
            (exactRationalLiteral (2091909201373137) 1600000000000000000),
            (exactRationalLiteral (2057184600680279) 400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-9198176893626791) 19200000000000000000),
            (exactRationalLiteral (-1037714415995493) 1600000000000000000),
            (exactRationalLiteral (-121218427220659) 80000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1097357795877107) 6400000000000000000),
            (exactRationalLiteral (641841915043727) 1600000000000000000),
            (exactRationalLiteral (215258522029833) 400000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (20033071550114327) 9600000000000000000),
            (exactRationalLiteral (573487569252623) 800000000000000000),
            (exactRationalLiteral (-30836248406509) 200000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2336663134519157) 3200000000000000000),
            (exactRationalLiteral (1056010194170371) 800000000000000000),
            (exactRationalLiteral (108577533177651) 200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-46728982124799383) 4800000000000000000),
            (exactRationalLiteral (-729505918767547) 400000000000000000),
            (exactRationalLiteral (-97118189677883) 100000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1181644768851619) 256000000000000000),
            (exactRationalLiteral (1393871917064381) 1600000000000000000),
            (exactRationalLiteral (23470022357559) 400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7978422922746023) 3840000000000000000),
            (exactRationalLiteral (1424750180481971) 320000000000000000),
            (exactRationalLiteral (-48202436351659) 400000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-262321504538811131) 19200000000000000000),
            (exactRationalLiteral (15060000390684123) 1600000000000000000),
            (exactRationalLiteral (141477168272197) 400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-889723549152499393) 19200000000000000000),
            (exactRationalLiteral (54335195132345613) 1600000000000000000),
            (exactRationalLiteral (1719173711771159) 400000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1164983255838906199) 9600000000000000000),
            (exactRationalLiteral (344961343456187111) 800000000000000000),
            (exactRationalLiteral (-28695695014803223) 200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (2755800093400664657) 2400000000000000000),
            (exactRationalLiteral (-38426517762859531) 20000000000000000),
            (exactRationalLiteral (1514807348058247) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-9674858865487824019) 6400000000000000000),
            (exactRationalLiteral (3777723100199456289) 1600000000000000000),
            (exactRationalLiteral (44344705333000587) 80000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (384190226287280617) 640000000000000000),
            (exactRationalLiteral (-752956070719734147) 800000000000000000),
            (exactRationalLiteral (-46230772874355933) 40000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-104625683264204203) 2400000000000000000),
            (exactRationalLiteral (-21479692218176373) 400000000000000000),
            (exactRationalLiteral (19804528733957911) 25000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-10737065927302296949) 19200000000000000000),
            (exactRationalLiteral (779867112034722141) 1600000000000000000),
            (exactRationalLiteral (-180731431947791173) 400000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5391527313489936847) 4800000000000000000),
            (exactRationalLiteral (-66083588603680559) 80000000000000000),
            (exactRationalLiteral (49777748629365223) 100000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-10737065927302296949) 19200000000000000000),
            (exactRationalLiteral (779867112034722141) 1600000000000000000),
            (exactRationalLiteral (-180731431947791173) 400000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-104625683264204203) 2400000000000000000),
            (exactRationalLiteral (-21479692218176373) 400000000000000000),
            (exactRationalLiteral (19804528733957911) 25000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (384190226287280617) 640000000000000000),
            (exactRationalLiteral (-752956070719734147) 800000000000000000),
            (exactRationalLiteral (-46230772874355933) 40000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9674858865487824019) 6400000000000000000),
            (exactRationalLiteral (3777723100199456289) 1600000000000000000),
            (exactRationalLiteral (44344705333000587) 80000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2755800093400664657) 2400000000000000000),
            (exactRationalLiteral (-38426517762859531) 20000000000000000),
            (exactRationalLiteral (1514807348058247) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-1164983255838906199) 9600000000000000000),
            (exactRationalLiteral (344961343456187111) 800000000000000000),
            (exactRationalLiteral (-28695695014803223) 200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-889723549152499393) 19200000000000000000),
            (exactRationalLiteral (54335195132345613) 1600000000000000000),
            (exactRationalLiteral (1719173711771159) 400000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-262321504538811131) 19200000000000000000),
            (exactRationalLiteral (15060000390684123) 1600000000000000000),
            (exactRationalLiteral (141477168272197) 400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7978422922746023) 3840000000000000000),
            (exactRationalLiteral (1424750180481971) 320000000000000000),
            (exactRationalLiteral (-48202436351659) 400000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1181644768851619) 256000000000000000),
            (exactRationalLiteral (1393871917064381) 1600000000000000000),
            (exactRationalLiteral (23470022357559) 400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-46728982124799383) 4800000000000000000),
            (exactRationalLiteral (-729505918767547) 400000000000000000),
            (exactRationalLiteral (-97118189677883) 100000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2336663134519157) 3200000000000000000),
            (exactRationalLiteral (1056010194170371) 800000000000000000),
            (exactRationalLiteral (108577533177651) 200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (20033071550114327) 9600000000000000000),
            (exactRationalLiteral (573487569252623) 800000000000000000),
            (exactRationalLiteral (-30836248406509) 200000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1097357795877107) 6400000000000000000),
            (exactRationalLiteral (641841915043727) 1600000000000000000),
            (exactRationalLiteral (215258522029833) 400000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9198176893626791) 19200000000000000000),
            (exactRationalLiteral (-1037714415995493) 1600000000000000000),
            (exactRationalLiteral (-121218427220659) 80000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-23392933815085561) 19200000000000000000),
            (exactRationalLiteral (2091909201373137) 1600000000000000000),
            (exactRationalLiteral (2057184600680279) 400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (19331800776779) 25000000000000000),
            (exactRationalLiteral (-1741890113884229) 200000000000000000),
            (exactRationalLiteral (-592355019068949) 25000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-138669066680526041) 9600000000000000000),
            (exactRationalLiteral (18104339594024109) 800000000000000000),
            (exactRationalLiteral (17795951618490127) 200000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (626834893890236857) 9600000000000000000),
            (exactRationalLiteral (1026203989747961) 32000000000000000),
            (exactRationalLiteral (-33671238587210003) 200000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-98299332731908153) 1600000000000000000),
            (exactRationalLiteral (-5477153164220367) 40000000000000000),
            (exactRationalLiteral (14945901414327363) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-80057884482759481) 9600000000000000000),
            (exactRationalLiteral (102238806462350399) 800000000000000000),
            (exactRationalLiteral (-9391681146817261) 200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (24128906906535711) 1280000000000000000),
            (exactRationalLiteral (-11382472682784933) 320000000000000000),
            (exactRationalLiteral (-818376924579507) 80000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 4800000000000000000),
            (exactRationalLiteral (-684347342461457) 400000000000000000),
            (exactRationalLiteral (684347342461457) 100000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (684347342461457) 600000000000000000),
          (exactRationalLiteral (4200852547840459) 160000000000000000),
          (exactRationalLiteral (12342573336230231) 300000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (14691278899161817) 200000000000000000),
          (exactRationalLiteral (2082599096115703) 120000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (277198409779271) 200000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (89580163839401873) 120000000000000000),
          (exactRationalLiteral (89778257934370627) 1200000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (819539810391990553) 600000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (89778257934370627) 1200000000000000000),
          (exactRationalLiteral (89580163839401873) 120000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (277198409779271) 200000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (2082599096115703) 120000000000000000),
          (exactRationalLiteral (14691278899161817) 200000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (12342573336230231) 300000000000000000),
          (exactRationalLiteral (4200852547840459) 160000000000000000),
          (exactRationalLiteral (684347342461457) 600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (45, 13),
      (45, 11),
      (45, 9),
      (45, 7),
      (45, 5),
      (45, 3),
      (45, 1),
      (44, 63),
      (44, 61),
      (44, 59),
      (44, 57),
      (44, 55),
      (44, 53),
      (44, 51),
      (44, 49),
      (44, 47),
      (44, 45),
      (44, 43),
      (44, 41),
      (44, 39),
      (44, 37),
      (44, 35),
      (44, 33),
      (44, 31),
      (44, 29),
      (44, 27),
      (44, 25),
      (44, 23),
      (44, 21),
      (44, 19),
      (44, 17),
      (44, 16),
      (44, 18),
      (44, 20),
      (44, 22),
      (44, 24),
      (44, 26),
      (44, 28),
      (44, 30),
      (44, 32),
      (44, 34),
      (44, 36),
      (44, 38),
      (44, 40),
      (44, 42),
      (44, 44),
      (44, 46),
      (44, 48),
      (44, 50),
      (44, 52),
      (44, 54),
      (44, 56),
      (44, 58)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  },
  {
    cubic :=
      {
        cell := 4
        lower := (0 : ℚ)
        width := (exactRationalLiteral (1) 4)
        centered := ![
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
            (exactRationalLiteral (234731138464279751) 38400000000000000000),
            (exactRationalLiteral (-33533019780611393) 1600000000000000000),
            (exactRationalLiteral (4790431397230199) 200000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (243989077426825873) 10240000000000000000),
            (exactRationalLiteral (52301318911760283) 1280000000000000000),
            (exactRationalLiteral (-17929488079420989) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-5685168566763805313) 76800000000000000000),
            (exactRationalLiteral (97113835013370091) 3200000000000000000),
            (exactRationalLiteral (81151640460840823) 400000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (774191556766925239) 19200000000000000000),
            (exactRationalLiteral (-605881726684457) 5000000000000000),
            (exactRationalLiteral (-17466298817306207) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (802206745746119281) 76800000000000000000),
            (exactRationalLiteral (60108259450692577) 640000000000000000),
            (exactRationalLiteral (27758297518686649) 400000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-173799647261713481) 25600000000000000000),
            (exactRationalLiteral (-84465918899105179) 3200000000000000000),
            (exactRationalLiteral (-4215247781939931) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5084723678395687) 19200000000000000000),
            (exactRationalLiteral (4040440393328969) 800000000000000000),
            (exactRationalLiteral (167819906502619) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-120452867292150983) 153600000000000000000),
            (exactRationalLiteral (-9501548249889007) 6400000000000000000),
            (exactRationalLiteral (-540532190284247) 800000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-69502261004877373) 153600000000000000000),
            (exactRationalLiteral (1424163138103603) 6400000000000000000),
            (exactRationalLiteral (3887204471579) 32000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (9580333177754023) 153600000000000000000),
            (exactRationalLiteral (369100684607823) 6400000000000000000),
            (exactRationalLiteral (9136351053751) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (122828317228672511) 76800000000000000000),
            (exactRationalLiteral (2590987996362347) 3200000000000000000),
            (exactRationalLiteral (2264952942647) 400000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9532877225233283) 76800000000000000000),
            (exactRationalLiteral (1947101379058839) 3200000000000000000),
            (exactRationalLiteral (238232813169227) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-343910211080539819) 38400000000000000000),
            (exactRationalLiteral (-1119463730209503) 1600000000000000000),
            (exactRationalLiteral (-165475609616371) 200000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-154706736052762607) 30720000000000000000),
            (exactRationalLiteral (1993088677628869) 6400000000000000000),
            (exactRationalLiteral (669539753410613) 800000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-146743193275932389) 30720000000000000000),
            (exactRationalLiteral (1017751132446751) 256000000000000000),
            (exactRationalLiteral (706649932397447) 800000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-964432115875740751) 51200000000000000000),
            (exactRationalLiteral (39879630820595627) 6400000000000000000),
            (exactRationalLiteral (3789119811883779) 800000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3245512811811628233) 51200000000000000000),
            (exactRationalLiteral (106260184501924597) 6400000000000000000),
            (exactRationalLiteral (18777771781949253) 800000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-28588710084215676577) 76800000000000000000),
            (exactRationalLiteral (807121109703356279) 3200000000000000000),
            (exactRationalLiteral (171936242853884879) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (6412017910475789851) 3200000000000000000),
            (exactRationalLiteral (-6763977734910477) 40000000000000000),
            (exactRationalLiteral (-29550430464381681) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-307686986034297935671) 153600000000000000000),
            (exactRationalLiteral (-12906474882427589119) 6400000000000000000),
            (exactRationalLiteral (1032005280663015397) 160000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (835177904592485297) 15360000000000000000),
            (exactRationalLiteral (12097497448342326037) 3200000000000000000),
            (exactRationalLiteral (-511911323500138639) 80000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (23012893152665415607) 38400000000000000000),
            (exactRationalLiteral (-3973362129874809147) 1600000000000000000),
            (exactRationalLiteral (619052442328757443) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-58270205117400043209) 51200000000000000000),
            (exactRationalLiteral (9736566371000661949) 6400000000000000000),
            (exactRationalLiteral (-961956720676772331) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (73449469221263886301) 38400000000000000000),
            (exactRationalLiteral (-584465822445600743) 320000000000000000),
            (exactRationalLiteral (220575970772148061) 200000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-58270205117400043209) 51200000000000000000),
            (exactRationalLiteral (9736566371000661949) 6400000000000000000),
            (exactRationalLiteral (-961956720676772331) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (23012893152665415607) 38400000000000000000),
            (exactRationalLiteral (-3973362129874809147) 1600000000000000000),
            (exactRationalLiteral (619052442328757443) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (835177904592485297) 15360000000000000000),
            (exactRationalLiteral (12097497448342326037) 3200000000000000000),
            (exactRationalLiteral (-511911323500138639) 80000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-307686986034297935671) 153600000000000000000),
            (exactRationalLiteral (-12906474882427589119) 6400000000000000000),
            (exactRationalLiteral (1032005280663015397) 160000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6412017910475789851) 3200000000000000000),
            (exactRationalLiteral (-6763977734910477) 40000000000000000),
            (exactRationalLiteral (-29550430464381681) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-28588710084215676577) 76800000000000000000),
            (exactRationalLiteral (807121109703356279) 3200000000000000000),
            (exactRationalLiteral (171936242853884879) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3245512811811628233) 51200000000000000000),
            (exactRationalLiteral (106260184501924597) 6400000000000000000),
            (exactRationalLiteral (18777771781949253) 800000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-964432115875740751) 51200000000000000000),
            (exactRationalLiteral (39879630820595627) 6400000000000000000),
            (exactRationalLiteral (3789119811883779) 800000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-146743193275932389) 30720000000000000000),
            (exactRationalLiteral (1017751132446751) 256000000000000000),
            (exactRationalLiteral (706649932397447) 800000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-154706736052762607) 30720000000000000000),
            (exactRationalLiteral (1993088677628869) 6400000000000000000),
            (exactRationalLiteral (669539753410613) 800000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-343910211080539819) 38400000000000000000),
            (exactRationalLiteral (-1119463730209503) 1600000000000000000),
            (exactRationalLiteral (-165475609616371) 200000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (9532877225233283) 76800000000000000000),
            (exactRationalLiteral (1947101379058839) 3200000000000000000),
            (exactRationalLiteral (238232813169227) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (122828317228672511) 76800000000000000000),
            (exactRationalLiteral (2590987996362347) 3200000000000000000),
            (exactRationalLiteral (2264952942647) 400000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9580333177754023) 153600000000000000000),
            (exactRationalLiteral (369100684607823) 6400000000000000000),
            (exactRationalLiteral (9136351053751) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-69502261004877373) 153600000000000000000),
            (exactRationalLiteral (1424163138103603) 6400000000000000000),
            (exactRationalLiteral (3887204471579) 32000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-120452867292150983) 153600000000000000000),
            (exactRationalLiteral (-9501548249889007) 6400000000000000000),
            (exactRationalLiteral (-540532190284247) 800000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (5084723678395687) 19200000000000000000),
            (exactRationalLiteral (4040440393328969) 800000000000000000),
            (exactRationalLiteral (167819906502619) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-173799647261713481) 25600000000000000000),
            (exactRationalLiteral (-84465918899105179) 3200000000000000000),
            (exactRationalLiteral (-4215247781939931) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (802206745746119281) 76800000000000000000),
            (exactRationalLiteral (60108259450692577) 640000000000000000),
            (exactRationalLiteral (27758297518686649) 400000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (774191556766925239) 19200000000000000000),
            (exactRationalLiteral (-605881726684457) 5000000000000000),
            (exactRationalLiteral (-17466298817306207) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-5685168566763805313) 76800000000000000000),
            (exactRationalLiteral (97113835013370091) 3200000000000000000),
            (exactRationalLiteral (81151640460840823) 400000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (243989077426825873) 10240000000000000000),
            (exactRationalLiteral (52301318911760283) 1280000000000000000),
            (exactRationalLiteral (-17929488079420989) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (234731138464279751) 38400000000000000000),
            (exactRationalLiteral (-33533019780611393) 1600000000000000000),
            (exactRationalLiteral (4790431397230199) 200000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (exactRationalLiteral (34930886317647829) 1280000000000000000),
          (exactRationalLiteral (91928453793576739) 1200000000000000000),
          (exactRationalLiteral (5240278380610517) 100000000000000000),
          (exactRationalLiteral (73670223963497773) 3200000000000000000),
          (exactRationalLiteral (97435126453061467) 9600000000000000000),
          (exactRationalLiteral (1075128536333423) 1200000000000000000),
          (exactRationalLiteral (18706016041792723) 19200000000000000000),
          (exactRationalLiteral (71505212116231) 150000000000000000),
          (exactRationalLiteral (1349915052917491) 19200000000000000000),
          (exactRationalLiteral (1088294071555303) 640000000000000000),
          (exactRationalLiteral (2010583031569337) 9600000000000000000),
          (exactRationalLiteral (8694269531349133) 960000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (76103558198870401) 37500000000000000),
          (exactRationalLiteral (41483705917704060787) 19200000000000000000),
          (exactRationalLiteral (26181459929894569) 50000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (161918727665951221) 75000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (26181459929894569) 50000000000000000),
          (exactRationalLiteral (41483705917704060787) 19200000000000000000),
          (exactRationalLiteral (76103558198870401) 37500000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (8694269531349133) 960000000000000000),
          (exactRationalLiteral (2010583031569337) 9600000000000000000),
          (exactRationalLiteral (1088294071555303) 640000000000000000),
          (exactRationalLiteral (1349915052917491) 19200000000000000000),
          (exactRationalLiteral (71505212116231) 150000000000000000),
          (exactRationalLiteral (18706016041792723) 19200000000000000000),
          (exactRationalLiteral (1075128536333423) 1200000000000000000),
          (exactRationalLiteral (97435126453061467) 9600000000000000000),
          (exactRationalLiteral (73670223963497773) 3200000000000000000),
          (exactRationalLiteral (5240278380610517) 100000000000000000),
          (exactRationalLiteral (91928453793576739) 1200000000000000000),
          (exactRationalLiteral (34930886317647829) 1280000000000000000),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (42, 62),
      (42, 58),
      (42, 54),
      (42, 50),
      (42, 46),
      (42, 42),
      (42, 38),
      (42, 34),
      (42, 30),
      (42, 26),
      (42, 22),
      (42, 18),
      (42, 14),
      (42, 10),
      (42, 6),
      (42, 2),
      (41, 62),
      (41, 58),
      (41, 54),
      (41, 50),
      (41, 46),
      (41, 42),
      (41, 38),
      (41, 34),
      (41, 30),
      (41, 26),
      (41, 22),
      (41, 18),
      (41, 14),
      (41, 10),
      (41, 6),
      (41, 9),
      (41, 13),
      (41, 17),
      (41, 21),
      (41, 25),
      (41, 29),
      (41, 33),
      (41, 37),
      (41, 41),
      (41, 45),
      (41, 49),
      (41, 53),
      (41, 57),
      (41, 61),
      (42, 1),
      (42, 5),
      (42, 9),
      (42, 13),
      (42, 17),
      (42, 21),
      (42, 25),
      (42, 29)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  },
  {
    cubic :=
      {
        cell := 4
        lower := (exactRationalLiteral (1) 4)
        width := (exactRationalLiteral (1) 4)
        centered := ![
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
            (exactRationalLiteral (684347342461457) 307200000000000000),
            (exactRationalLiteral (-684347342461457) 64000000000000000),
            (exactRationalLiteral (684347342461457) 40000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (285563221188802203) 10240000000000000000),
            (exactRationalLiteral (-6382446021714093) 1280000000000000000),
            (exactRationalLiteral (-11412394387316199) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-4288561875560655443) 76800000000000000000),
            (exactRationalLiteral (341772394653153107) 3200000000000000000),
            (exactRationalLiteral (8235527871810137) 80000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (11603011237595249) 6400000000000000000),
            (exactRationalLiteral (-35219127838357773) 200000000000000000),
            (exactRationalLiteral (-4501418724652779) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (2786392859982165731) 76800000000000000000),
            (exactRationalLiteral (335493867573724157) 3200000000000000000),
            (exactRationalLiteral (-10282012358556013) 400000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1015085986932778393) 76800000000000000000),
            (exactRationalLiteral (-13896237842345751) 640000000000000000),
            (exactRationalLiteral (11707612625628143) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1818774729597031) 1280000000000000000),
            (exactRationalLiteral (2681928033116713) 800000000000000000),
            (exactRationalLiteral (-847076086608747) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-176500700848264301) 153600000000000000000),
            (exactRationalLiteral (-7939755897710151) 6400000000000000000),
            (exactRationalLiteral (52857134654947) 32000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-61886103849175759) 153600000000000000000),
            (exactRationalLiteral (765392078064651) 6400000000000000000),
            (exactRationalLiteral (-426565641808951) 800000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (4192927535618479) 51200000000000000000),
            (exactRationalLiteral (742750643227559) 6400000000000000000),
            (exactRationalLiteral (177688628256117) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (138299124722549293) 76800000000000000000),
            (exactRationalLiteral (2548897848328403) 3200000000000000000),
            (exactRationalLiteral (-23310026959619) 400000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8013518287571587) 25600000000000000000),
            (exactRationalLiteral (2883170434284607) 3200000000000000000),
            (exactRationalLiteral (229801714443657) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-352658718008776321) 38400000000000000000),
            (exactRationalLiteral (-1804374784466503) 1600000000000000000),
            (exactRationalLiteral (-176979917512129) 200000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-251512276897008419) 51200000000000000000),
            (exactRationalLiteral (166926716972597) 256000000000000000),
            (exactRationalLiteral (84099973986483) 160000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-114771677002408231) 30720000000000000000),
            (exactRationalLiteral (27627934196677951) 6400000000000000000),
            (exactRationalLiteral (385428010357141) 800000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2614158989721586159) 153600000000000000000),
            (exactRationalLiteral (10446235537571847) 1280000000000000000),
            (exactRationalLiteral (95466144869921) 32000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8898187146013397177) 153600000000000000000),
            (exactRationalLiteral (169099732142996061) 6400000000000000000),
            (exactRationalLiteral (12642002038586479) 800000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-881986908974500259) 3072000000000000000),
            (exactRationalLiteral (262280794962420547) 640000000000000000),
            (exactRationalLiteral (80205189700488349) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (17305711141969359497) 9600000000000000000),
            (exactRationalLiteral (-267193717693489339) 200000000000000000),
            (exactRationalLiteral (-85621676697028549) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-110250681816352886783) 51200000000000000000),
            (exactRationalLiteral (3960367250844661929) 6400000000000000000),
            (exactRationalLiteral (3273394663321048539) 800000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16467264341673159517) 25600000000000000000),
            (exactRationalLiteral (3537070089345260349) 3200000000000000000),
            (exactRationalLiteral (-1720657061997839649) 400000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5864363741430299393) 38400000000000000000),
            (exactRationalLiteral (-1865645330525454699) 1600000000000000000),
            (exactRationalLiteral (434805957345919781) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-126973907603467521929) 153600000000000000000),
            (exactRationalLiteral (6369134573718524613) 6400000000000000000),
            (exactRationalLiteral (-721759177964296337) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (58368773439540172559) 38400000000000000000),
            (exactRationalLiteral (-2136841607950145563) 1600000000000000000),
            (exactRationalLiteral (34433556273356203) 40000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-126973907603467521929) 153600000000000000000),
            (exactRationalLiteral (6369134573718524613) 6400000000000000000),
            (exactRationalLiteral (-721759177964296337) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5864363741430299393) 38400000000000000000),
            (exactRationalLiteral (-1865645330525454699) 1600000000000000000),
            (exactRationalLiteral (434805957345919781) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (16467264341673159517) 25600000000000000000),
            (exactRationalLiteral (3537070089345260349) 3200000000000000000),
            (exactRationalLiteral (-1720657061997839649) 400000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-110250681816352886783) 51200000000000000000),
            (exactRationalLiteral (3960367250844661929) 6400000000000000000),
            (exactRationalLiteral (3273394663321048539) 800000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (17305711141969359497) 9600000000000000000),
            (exactRationalLiteral (-267193717693489339) 200000000000000000),
            (exactRationalLiteral (-85621676697028549) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-881986908974500259) 3072000000000000000),
            (exactRationalLiteral (262280794962420547) 640000000000000000),
            (exactRationalLiteral (80205189700488349) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-8898187146013397177) 153600000000000000000),
            (exactRationalLiteral (169099732142996061) 6400000000000000000),
            (exactRationalLiteral (12642002038586479) 800000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2614158989721586159) 153600000000000000000),
            (exactRationalLiteral (10446235537571847) 1280000000000000000),
            (exactRationalLiteral (95466144869921) 32000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-114771677002408231) 30720000000000000000),
            (exactRationalLiteral (27627934196677951) 6400000000000000000),
            (exactRationalLiteral (385428010357141) 800000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-251512276897008419) 51200000000000000000),
            (exactRationalLiteral (166926716972597) 256000000000000000),
            (exactRationalLiteral (84099973986483) 160000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-352658718008776321) 38400000000000000000),
            (exactRationalLiteral (-1804374784466503) 1600000000000000000),
            (exactRationalLiteral (-176979917512129) 200000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (8013518287571587) 25600000000000000000),
            (exactRationalLiteral (2883170434284607) 3200000000000000000),
            (exactRationalLiteral (229801714443657) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (138299124722549293) 76800000000000000000),
            (exactRationalLiteral (2548897848328403) 3200000000000000000),
            (exactRationalLiteral (-23310026959619) 400000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4192927535618479) 51200000000000000000),
            (exactRationalLiteral (742750643227559) 6400000000000000000),
            (exactRationalLiteral (177688628256117) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-61886103849175759) 153600000000000000000),
            (exactRationalLiteral (765392078064651) 6400000000000000000),
            (exactRationalLiteral (-426565641808951) 800000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-176500700848264301) 153600000000000000000),
            (exactRationalLiteral (-7939755897710151) 6400000000000000000),
            (exactRationalLiteral (52857134654947) 32000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1818774729597031) 1280000000000000000),
            (exactRationalLiteral (2681928033116713) 800000000000000000),
            (exactRationalLiteral (-847076086608747) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1015085986932778393) 76800000000000000000),
            (exactRationalLiteral (-13896237842345751) 640000000000000000),
            (exactRationalLiteral (11707612625628143) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2786392859982165731) 76800000000000000000),
            (exactRationalLiteral (335493867573724157) 3200000000000000000),
            (exactRationalLiteral (-10282012358556013) 400000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (11603011237595249) 6400000000000000000),
            (exactRationalLiteral (-35219127838357773) 200000000000000000),
            (exactRationalLiteral (-4501418724652779) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-4288561875560655443) 76800000000000000000),
            (exactRationalLiteral (341772394653153107) 3200000000000000000),
            (exactRationalLiteral (8235527871810137) 80000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (285563221188802203) 10240000000000000000),
            (exactRationalLiteral (-6382446021714093) 1280000000000000000),
            (exactRationalLiteral (-11412394387316199) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 307200000000000000),
            (exactRationalLiteral (-684347342461457) 64000000000000000),
            (exactRationalLiteral (684347342461457) 40000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (6159126082153113) 1600000000000000000),
          (exactRationalLiteral (18286313558781027) 640000000000000000),
          (exactRationalLiteral (129258978522301691) 1920000000000000000),
          (exactRationalLiteral (109362967888198493) 4800000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (8150013016499669) 19200000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (95708789364054211) 19200000000000000000),
          (exactRationalLiteral (27309387192082643) 6400000000000000000),
          (exactRationalLiteral (345373916103106489) 19200000000000000000),
          (exactRationalLiteral (1170561556431868067) 19200000000000000000),
          (exactRationalLiteral (1070725148046693807) 3200000000000000000),
          (exactRationalLiteral (4655235795056692489) 2400000000000000000),
          (exactRationalLiteral (4236614040415267313) 1920000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (33483960540457921) 100000000000000000),
          (exactRationalLiteral (18545835953734027847) 19200000000000000000),
          (exactRationalLiteral (2721666904258068159) 1600000000000000000),
          (exactRationalLiteral (18545835953734027847) 19200000000000000000),
          (exactRationalLiteral (33483960540457921) 100000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (4236614040415267313) 1920000000000000000),
          (exactRationalLiteral (4655235795056692489) 2400000000000000000),
          (exactRationalLiteral (1070725148046693807) 3200000000000000000),
          (exactRationalLiteral (1170561556431868067) 19200000000000000000),
          (exactRationalLiteral (345373916103106489) 19200000000000000000),
          (exactRationalLiteral (27309387192082643) 6400000000000000000),
          (exactRationalLiteral (95708789364054211) 19200000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (8150013016499669) 19200000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (109362967888198493) 4800000000000000000),
          (exactRationalLiteral (129258978522301691) 1920000000000000000),
          (exactRationalLiteral (18286313558781027) 640000000000000000),
          (exactRationalLiteral (6159126082153113) 1600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (42, 63),
      (42, 59),
      (42, 55),
      (42, 51),
      (42, 47),
      (42, 43),
      (42, 39),
      (42, 35),
      (42, 31),
      (42, 27),
      (42, 23),
      (42, 19),
      (42, 15),
      (42, 11),
      (42, 7),
      (42, 3),
      (41, 63),
      (41, 59),
      (41, 55),
      (41, 51),
      (41, 47),
      (41, 43),
      (41, 39),
      (41, 35),
      (41, 31),
      (41, 27),
      (41, 23),
      (41, 19),
      (41, 15),
      (41, 11),
      (41, 7),
      (41, 8),
      (41, 12),
      (41, 16),
      (41, 20),
      (41, 24),
      (41, 28),
      (41, 32),
      (41, 36),
      (41, 40),
      (41, 44),
      (41, 48),
      (41, 52),
      (41, 56),
      (41, 60),
      (42, 0),
      (42, 4),
      (42, 8),
      (42, 12),
      (42, 16),
      (42, 20),
      (42, 24),
      (42, 28)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  },
  {
    cubic :=
      {
        cell := 4
        lower := (exactRationalLiteral (1) 2)
        width := (exactRationalLiteral (1) 4)
        centered := ![
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
            (exactRationalLiteral (6159126082153113) 12800000000000000000),
            (exactRationalLiteral (-6159126082153113) 1600000000000000000),
            (exactRationalLiteral (2053042027384371) 200000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (235838209852248941) 10240000000000000000),
            (exactRationalLiteral (-38997836186769309) 1280000000000000000),
            (exactRationalLiteral (-4895300695211409) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-1903691839740289133) 76800000000000000000),
            (exactRationalLiteral (426534949885775571) 3200000000000000000),
            (exactRationalLiteral (1203638257260547) 400000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-812607538733020441) 19200000000000000000),
            (exactRationalLiteral (-16619053258341919) 100000000000000000),
            (exactRationalLiteral (8463461368000649) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (1507936892537622623) 25600000000000000000),
            (exactRationalLiteral (218285198385014781) 3200000000000000000),
            (exactRationalLiteral (-1932892889431947) 16000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1227790329065340911) 76800000000000000000),
            (exactRationalLiteral (1838996421183993) 640000000000000000),
            (exactRationalLiteral (27630473033196217) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5829738426181063) 3840000000000000000),
            (exactRationalLiteral (-2736168299541007) 800000000000000000),
            (exactRationalLiteral (-1861972079720113) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-200834253611409419) 153600000000000000000),
            (exactRationalLiteral (1069878681100393) 6400000000000000000),
            (exactRationalLiteral (3183388923031597) 800000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-64507522096888969) 153600000000000000000),
            (exactRationalLiteral (-397672399273601) 1280000000000000000),
            (exactRationalLiteral (-950311395407377) 800000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (19841759114103659) 153600000000000000000),
            (exactRationalLiteral (1790609710656759) 6400000000000000000),
            (exactRationalLiteral (346240905458483) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (51070163856465073) 25600000000000000000),
            (exactRationalLiteral (480901556137079) 640000000000000000),
            (exactRationalLiteral (-9777001372377) 80000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (44063473646844007) 76800000000000000000),
            (exactRationalLiteral (757103018921619) 640000000000000000),
            (exactRationalLiteral (221370615718087) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-365654742957303919) 38400000000000000000),
            (exactRationalLiteral (-507060614061307) 320000000000000000),
            (exactRationalLiteral (-188484225407887) 200000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-725447984239859519) 153600000000000000000),
            (exactRationalLiteral (5357087637088189) 6400000000000000000),
            (exactRationalLiteral (171459986454217) 800000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-134916843798616327) 51200000000000000000),
            (exactRationalLiteral (28527202394025903) 6400000000000000000),
            (exactRationalLiteral (12841217663367) 160000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-455548388978799493) 30720000000000000000),
            (exactRationalLiteral (58972859794579827) 6400000000000000000),
            (exactRationalLiteral (984187431612271) 800000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7756427807665834159) 153600000000000000000),
            (exactRationalLiteral (207396200810616429) 6400000000000000000),
            (exactRationalLiteral (1301246459044741) 160000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4528570270565871999) 25600000000000000000),
            (exactRationalLiteral (1448762627307263071) 3200000000000000000),
            (exactRationalLiteral (-11525863452908181) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (2664089662356532853) 1920000000000000000),
            (exactRationalLiteral (-376306595462666581) 200000000000000000),
            (exactRationalLiteral (-23491201072148693) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-275255632944114220091) 153600000000000000000),
            (exactRationalLiteral (13280682424140799193) 6400000000000000000),
            (exactRationalLiteral (1386762923327020093) 800000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (53331927039128379041) 76800000000000000000),
            (exactRationalLiteral (-333551809528078231) 640000000000000000),
            (exactRationalLiteral (-881757506494986103) 400000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-282940897834247359) 12800000000000000000),
            (exactRationalLiteral (-494914471107450899) 1600000000000000000),
            (exactRationalLiteral (250559472363082119) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-96459420125878026319) 153600000000000000000),
            (exactRationalLiteral (3962492947286291253) 6400000000000000000),
            (exactRationalLiteral (-481561635251820343) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (15806701470206401059) 12800000000000000000),
            (exactRationalLiteral (-308997372258751119) 320000000000000000),
            (exactRationalLiteral (123759591961413969) 200000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-96459420125878026319) 153600000000000000000),
            (exactRationalLiteral (3962492947286291253) 6400000000000000000),
            (exactRationalLiteral (-481561635251820343) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-282940897834247359) 12800000000000000000),
            (exactRationalLiteral (-494914471107450899) 1600000000000000000),
            (exactRationalLiteral (250559472363082119) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (53331927039128379041) 76800000000000000000),
            (exactRationalLiteral (-333551809528078231) 640000000000000000),
            (exactRationalLiteral (-881757506494986103) 400000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-275255632944114220091) 153600000000000000000),
            (exactRationalLiteral (13280682424140799193) 6400000000000000000),
            (exactRationalLiteral (1386762923327020093) 800000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2664089662356532853) 1920000000000000000),
            (exactRationalLiteral (-376306595462666581) 200000000000000000),
            (exactRationalLiteral (-23491201072148693) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-4528570270565871999) 25600000000000000000),
            (exactRationalLiteral (1448762627307263071) 3200000000000000000),
            (exactRationalLiteral (-11525863452908181) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-7756427807665834159) 153600000000000000000),
            (exactRationalLiteral (207396200810616429) 6400000000000000000),
            (exactRationalLiteral (1301246459044741) 160000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-455548388978799493) 30720000000000000000),
            (exactRationalLiteral (58972859794579827) 6400000000000000000),
            (exactRationalLiteral (984187431612271) 800000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-134916843798616327) 51200000000000000000),
            (exactRationalLiteral (28527202394025903) 6400000000000000000),
            (exactRationalLiteral (12841217663367) 160000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-725447984239859519) 153600000000000000000),
            (exactRationalLiteral (5357087637088189) 6400000000000000000),
            (exactRationalLiteral (171459986454217) 800000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-365654742957303919) 38400000000000000000),
            (exactRationalLiteral (-507060614061307) 320000000000000000),
            (exactRationalLiteral (-188484225407887) 200000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (44063473646844007) 76800000000000000000),
            (exactRationalLiteral (757103018921619) 640000000000000000),
            (exactRationalLiteral (221370615718087) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (51070163856465073) 25600000000000000000),
            (exactRationalLiteral (480901556137079) 640000000000000000),
            (exactRationalLiteral (-9777001372377) 80000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (19841759114103659) 153600000000000000000),
            (exactRationalLiteral (1790609710656759) 6400000000000000000),
            (exactRationalLiteral (346240905458483) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-64507522096888969) 153600000000000000000),
            (exactRationalLiteral (-397672399273601) 1280000000000000000),
            (exactRationalLiteral (-950311395407377) 800000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-200834253611409419) 153600000000000000000),
            (exactRationalLiteral (1069878681100393) 6400000000000000000),
            (exactRationalLiteral (3183388923031597) 800000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (5829738426181063) 3840000000000000000),
            (exactRationalLiteral (-2736168299541007) 800000000000000000),
            (exactRationalLiteral (-1861972079720113) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1227790329065340911) 76800000000000000000),
            (exactRationalLiteral (1838996421183993) 640000000000000000),
            (exactRationalLiteral (27630473033196217) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1507936892537622623) 25600000000000000000),
            (exactRationalLiteral (218285198385014781) 3200000000000000000),
            (exactRationalLiteral (-1932892889431947) 16000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-812607538733020441) 19200000000000000000),
            (exactRationalLiteral (-16619053258341919) 100000000000000000),
            (exactRationalLiteral (8463461368000649) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-1903691839740289133) 76800000000000000000),
            (exactRationalLiteral (426534949885775571) 3200000000000000000),
            (exactRationalLiteral (1203638257260547) 400000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (235838209852248941) 10240000000000000000),
            (exactRationalLiteral (-38997836186769309) 1280000000000000000),
            (exactRationalLiteral (-4895300695211409) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (6159126082153113) 12800000000000000000),
            (exactRationalLiteral (-6159126082153113) 1600000000000000000),
            (exactRationalLiteral (2053042027384371) 200000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (684347342461457) 600000000000000000),
          (exactRationalLiteral (4200852547840459) 160000000000000000),
          (exactRationalLiteral (12342573336230231) 300000000000000000),
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (39270448562521033) 2400000000000000000),
          (exactRationalLiteral (32460336439073) 18750000000000000),
          (exactRationalLiteral (6379891904287889) 4800000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (586467639281408157) 800000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (819539810391990553) 600000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (586467639281408157) 800000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (6379891904287889) 4800000000000000000),
          (exactRationalLiteral (32460336439073) 18750000000000000),
          (exactRationalLiteral (39270448562521033) 2400000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (12342573336230231) 300000000000000000),
          (exactRationalLiteral (4200852547840459) 160000000000000000),
          (exactRationalLiteral (684347342461457) 600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 0),
      (42, 60),
      (42, 56),
      (42, 52),
      (42, 48),
      (42, 44),
      (42, 40),
      (42, 36),
      (42, 32),
      (42, 28),
      (42, 24),
      (42, 20),
      (42, 16),
      (42, 12),
      (42, 8),
      (42, 4),
      (42, 0),
      (41, 60),
      (41, 56),
      (41, 52),
      (41, 48),
      (41, 44),
      (41, 40),
      (41, 36),
      (41, 32),
      (41, 28),
      (41, 24),
      (41, 20),
      (41, 16),
      (41, 12),
      (41, 8),
      (41, 7),
      (41, 11),
      (41, 15),
      (41, 19),
      (41, 23),
      (41, 27),
      (41, 31),
      (41, 35),
      (41, 39),
      (41, 43),
      (41, 47),
      (41, 51),
      (41, 55),
      (41, 59),
      (41, 63),
      (42, 3),
      (42, 7),
      (42, 11),
      (42, 15),
      (42, 19),
      (42, 23),
      (42, 27)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  },
  {
    cubic :=
      {
        cell := 4
        lower := (exactRationalLiteral (3) 4)
        width := (exactRationalLiteral (1) 4)
        centered := ![
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
            (exactRationalLiteral (684347342461457) 38400000000000000000),
            (exactRationalLiteral (-684347342461457) 1600000000000000000),
            (exactRationalLiteral (684347342461457) 200000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (146950792954004407) 10240000000000000000),
            (exactRationalLiteral (-9108970316681073) 256000000000000000),
            (exactRationalLiteral (1621792996893381) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (102013102850866061) 15360000000000000000),
            (exactRationalLiteral (351401500711237483) 3200000000000000000),
            (exactRationalLiteral (-38770362844529591) 400000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1456901038346811053) 19200000000000000000),
            (exactRationalLiteral (-731688204094259) 8000000000000000),
            (exactRationalLiteral (21428341460654077) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (5101492761584401807) 76800000000000000000),
            (exactRationalLiteral (-51084710312665243) 3200000000000000000),
            (exactRationalLiteral (-86362632113041337) 400000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-259121106133731407) 25600000000000000000),
            (exactRationalLiteral (151562595053840981) 3200000000000000000),
            (exactRationalLiteral (43553333440764291) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-13671566595427547) 19200000000000000000),
            (exactRationalLiteral (-12213848604644191) 800000000000000000),
            (exactRationalLiteral (-2876868072831479) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-148766472221796209) 153600000000000000000),
            (exactRationalLiteral (140218843892341) 51200000000000000),
            (exactRationalLiteral (5045349479689519) 800000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-89936413834379227) 153600000000000000000),
            (exactRationalLiteral (-1367419817038873) 1280000000000000000),
            (exactRationalLiteral (-1474057149005803) 800000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (35414517352355473) 153600000000000000000),
            (exactRationalLiteral (3512677886895423) 6400000000000000000),
            (exactRationalLiteral (514793182660849) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (33389723650311181) 15360000000000000000),
            (exactRationalLiteral (2157817793433323) 3200000000000000000),
            (exactRationalLiteral (-74459986764151) 400000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (69399287208207341) 76800000000000000000),
            (exactRationalLiteral (4654135360029303) 3200000000000000000),
            (exactRationalLiteral (212939516992517) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-76634877863124161) 7680000000000000000),
            (exactRationalLiteral (-3312248587729599) 1600000000000000000),
            (exactRationalLiteral (-39997706660729) 40000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-692244098113792573) 153600000000000000000),
            (exactRationalLiteral (5544847815948661) 6400000000000000000),
            (exactRationalLiteral (-77579897023981) 800000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-234101731660052767) 153600000000000000000),
            (exactRationalLiteral (28141582903212631) 6400000000000000000),
            (exactRationalLiteral (-257015833723471) 800000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-639234800569238089) 51200000000000000000),
            (exactRationalLiteral (60104677140757403) 6400000000000000000),
            (exactRationalLiteral (-418278758523483) 800000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2152839631410967407) 51200000000000000000),
            (exactRationalLiteral (221149590504785701) 6400000000000000000),
            (exactRationalLiteral (370462551860931) 800000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5398369621902521863) 76800000000000000000),
            (exactRationalLiteral (1219197067188837287) 3200000000000000000),
            (exactRationalLiteral (-103256916606304711) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (2923798885288133467) 3200000000000000000),
            (exactRationalLiteral (-361158521982084111) 200000000000000000),
            (exactRationalLiteral (38639274552731163) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-186476910279321297601) 153600000000000000000),
            (exactRationalLiteral (15054470637460822673) 6400000000000000000),
            (exactRationalLiteral (-499868816667008353) 800000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (36099880897357613059) 76800000000000000000),
            (exactRationalLiteral (-140679598504585139) 128000000000000000),
            (exactRationalLiteral (-42857950992132557) 400000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1548581791721812691) 38400000000000000000),
            (exactRationalLiteral (138830448379202253) 1600000000000000000),
            (exactRationalLiteral (66312987380244457) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-25834137298110739647) 51200000000000000000),
            (exactRationalLiteral (2516641491703961869) 6400000000000000000),
            (exactRationalLiteral (-241364092539344349) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (39441665588772169051) 38400000000000000000),
            (exactRationalLiteral (-1146764872258833811) 1600000000000000000),
            (exactRationalLiteral (75351402556046923) 200000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-25834137298110739647) 51200000000000000000),
            (exactRationalLiteral (2516641491703961869) 6400000000000000000),
            (exactRationalLiteral (-241364092539344349) 800000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1548581791721812691) 38400000000000000000),
            (exactRationalLiteral (138830448379202253) 1600000000000000000),
            (exactRationalLiteral (66312987380244457) 200000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (36099880897357613059) 76800000000000000000),
            (exactRationalLiteral (-140679598504585139) 128000000000000000),
            (exactRationalLiteral (-42857950992132557) 400000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-186476910279321297601) 153600000000000000000),
            (exactRationalLiteral (15054470637460822673) 6400000000000000000),
            (exactRationalLiteral (-499868816667008353) 800000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2923798885288133467) 3200000000000000000),
            (exactRationalLiteral (-361158521982084111) 200000000000000000),
            (exactRationalLiteral (38639274552731163) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-5398369621902521863) 76800000000000000000),
            (exactRationalLiteral (1219197067188837287) 3200000000000000000),
            (exactRationalLiteral (-103256916606304711) 400000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2152839631410967407) 51200000000000000000),
            (exactRationalLiteral (221149590504785701) 6400000000000000000),
            (exactRationalLiteral (370462551860931) 800000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-639234800569238089) 51200000000000000000),
            (exactRationalLiteral (60104677140757403) 6400000000000000000),
            (exactRationalLiteral (-418278758523483) 800000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-234101731660052767) 153600000000000000000),
            (exactRationalLiteral (28141582903212631) 6400000000000000000),
            (exactRationalLiteral (-257015833723471) 800000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-692244098113792573) 153600000000000000000),
            (exactRationalLiteral (5544847815948661) 6400000000000000000),
            (exactRationalLiteral (-77579897023981) 800000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-76634877863124161) 7680000000000000000),
            (exactRationalLiteral (-3312248587729599) 1600000000000000000),
            (exactRationalLiteral (-39997706660729) 40000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (69399287208207341) 76800000000000000000),
            (exactRationalLiteral (4654135360029303) 3200000000000000000),
            (exactRationalLiteral (212939516992517) 400000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (33389723650311181) 15360000000000000000),
            (exactRationalLiteral (2157817793433323) 3200000000000000000),
            (exactRationalLiteral (-74459986764151) 400000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (35414517352355473) 153600000000000000000),
            (exactRationalLiteral (3512677886895423) 6400000000000000000),
            (exactRationalLiteral (514793182660849) 800000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-89936413834379227) 153600000000000000000),
            (exactRationalLiteral (-1367419817038873) 1280000000000000000),
            (exactRationalLiteral (-1474057149005803) 800000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-148766472221796209) 153600000000000000000),
            (exactRationalLiteral (140218843892341) 51200000000000000),
            (exactRationalLiteral (5045349479689519) 800000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-13671566595427547) 19200000000000000000),
            (exactRationalLiteral (-12213848604644191) 800000000000000000),
            (exactRationalLiteral (-2876868072831479) 100000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-259121106133731407) 25600000000000000000),
            (exactRationalLiteral (151562595053840981) 3200000000000000000),
            (exactRationalLiteral (43553333440764291) 400000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5101492761584401807) 76800000000000000000),
            (exactRationalLiteral (-51084710312665243) 3200000000000000000),
            (exactRationalLiteral (-86362632113041337) 400000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1456901038346811053) 19200000000000000000),
            (exactRationalLiteral (-731688204094259) 8000000000000000),
            (exactRationalLiteral (21428341460654077) 100000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (102013102850866061) 15360000000000000000),
            (exactRationalLiteral (351401500711237483) 3200000000000000000),
            (exactRationalLiteral (-38770362844529591) 400000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (146950792954004407) 10240000000000000000),
            (exactRationalLiteral (-9108970316681073) 256000000000000000),
            (exactRationalLiteral (1621792996893381) 160000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 38400000000000000000),
            (exactRationalLiteral (-684347342461457) 1600000000000000000),
            (exactRationalLiteral (684347342461457) 200000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (684347342461457) 4800000000000000000),
          (exactRationalLiteral (24128906906535711) 1280000000000000000),
          (exactRationalLiteral (5578015341029527) 300000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (108748332272322647) 1600000000000000000),
          (exactRationalLiteral (138669066680526041) 9600000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (23392933815085561) 19200000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (1181644768851619) 256000000000000000),
          (exactRationalLiteral (7978422922746023) 3840000000000000000),
          (exactRationalLiteral (262321504538811131) 19200000000000000000),
          (exactRationalLiteral (889723549152499393) 19200000000000000000),
          (exactRationalLiteral (1164983255838906199) 9600000000000000000),
          (exactRationalLiteral (2755800093400664657) 2400000000000000000),
          (exactRationalLiteral (9674858865487824019) 6400000000000000000),
          (exactRationalLiteral (384190226287280617) 640000000000000000),
          (exactRationalLiteral (230731058746584779) 4800000000000000000),
          (exactRationalLiteral (10737065927302296949) 19200000000000000000),
          (exactRationalLiteral (5391527313489936847) 4800000000000000000),
          (exactRationalLiteral (10737065927302296949) 19200000000000000000),
          (exactRationalLiteral (230731058746584779) 4800000000000000000),
          (exactRationalLiteral (384190226287280617) 640000000000000000),
          (exactRationalLiteral (9674858865487824019) 6400000000000000000),
          (exactRationalLiteral (2755800093400664657) 2400000000000000000),
          (exactRationalLiteral (1164983255838906199) 9600000000000000000),
          (exactRationalLiteral (889723549152499393) 19200000000000000000),
          (exactRationalLiteral (262321504538811131) 19200000000000000000),
          (exactRationalLiteral (7978422922746023) 3840000000000000000),
          (exactRationalLiteral (1181644768851619) 256000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (23392933815085561) 19200000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (138669066680526041) 9600000000000000000),
          (exactRationalLiteral (108748332272322647) 1600000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (5578015341029527) 300000000000000000),
          (exactRationalLiteral (24128906906535711) 1280000000000000000),
          (exactRationalLiteral (684347342461457) 4800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 1),
      (42, 61),
      (42, 57),
      (42, 53),
      (42, 49),
      (42, 45),
      (42, 41),
      (42, 37),
      (42, 33),
      (42, 29),
      (42, 25),
      (42, 21),
      (42, 17),
      (42, 13),
      (42, 9),
      (42, 5),
      (42, 1),
      (41, 61),
      (41, 57),
      (41, 53),
      (41, 49),
      (41, 45),
      (41, 41),
      (41, 37),
      (41, 33),
      (41, 29),
      (41, 25),
      (41, 21),
      (41, 17),
      (41, 13),
      (41, 9),
      (41, 6),
      (41, 10),
      (41, 14),
      (41, 18),
      (41, 22),
      (41, 26),
      (41, 30),
      (41, 34),
      (41, 38),
      (41, 42),
      (41, 46),
      (41, 50),
      (41, 54),
      (41, 58),
      (41, 62),
      (42, 2),
      (42, 6),
      (42, 10),
      (42, 14),
      (42, 18),
      (42, 22),
      (42, 26)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  },
  {
    cubic :=
      {
        cell := 4
        lower := (0 : ℚ)
        width := (exactRationalLiteral (1) 8)
        centered := ![
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
            (exactRationalLiteral (6159126082153113) 819200000000000000),
            (exactRationalLiteral (-6159126082153113) 256000000000000000),
            (exactRationalLiteral (2053042027384371) 80000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1705762185326706409) 81920000000000000000),
            (exactRationalLiteral (284181774810777483) 5120000000000000000),
            (exactRationalLiteral (-39117523004894373) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-46139817710954943589) 614400000000000000000),
            (exactRationalLiteral (43861777659222003) 12800000000000000000),
            (exactRationalLiteral (36458056294515343) 160000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1811386284104848849) 38400000000000000000),
            (exactRationalLiteral (-155708334881250469) 1600000000000000000),
            (exactRationalLiteral (-5176879710117391) 25000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (998909446326046951) 204800000000000000000),
            (exactRationalLiteral (1072111844000483613) 12800000000000000000),
            (exactRationalLiteral (74536749975994629) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3190853424387285019) 614400000000000000000),
            (exactRationalLiteral (-62608250852975391) 2560000000000000000),
            (exactRationalLiteral (-16391925767663899) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1258625571442147) 30720000000000000000),
            (exactRationalLiteral (14983033950749717) 3200000000000000000),
            (exactRationalLiteral (843087809560921) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-853778532758574223) 1228800000000000000000),
            (exactRationalLiteral (-34913083960090079) 25600000000000000000),
            (exactRationalLiteral (-402408931779491) 320000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-572263092148726157) 1228800000000000000000),
            (exactRationalLiteral (5046059228457299) 25600000000000000000),
            (exactRationalLiteral (456233100378163) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (72183999174459631) 1228800000000000000000),
            (exactRationalLiteral (1524133472817471) 25600000000000000000),
            (exactRationalLiteral (-66003436493681) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (317187019693546313) 204800000000000000000),
            (exactRationalLiteral (10342104683727667) 12800000000000000000),
            (exactRationalLiteral (17317395836427) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (54331413681538343) 614400000000000000000),
            (exactRationalLiteral (6831258714195663) 12800000000000000000),
            (exactRationalLiteral (480681175701239) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2738835225385554863) 307200000000000000000),
            (exactRationalLiteral (-3821704636320407) 6400000000000000000),
            (exactRationalLiteral (-325199065284863) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-6208044747779847931) 1228800000000000000000),
            (exactRationalLiteral (206787030205357) 1024000000000000000),
            (exactRationalLiteral (58543977942413) 64000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-82275367469545547) 16384000000000000000),
            (exactRationalLiteral (98787902554065159) 25600000000000000000),
            (exactRationalLiteral (1573910825815047) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23601490398898554997) 1228800000000000000000),
            (exactRationalLiteral (28732162187955903) 5120000000000000000),
            (exactRationalLiteral (1655894543767087) 320000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-79051695181938795851) 1228800000000000000000),
            (exactRationalLiteral (346861766008219989) 25600000000000000000),
            (exactRationalLiteral (40623428435579893) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3164235346752875739) 8192000000000000000),
            (exactRationalLiteral (498974788164237467) 2560000000000000000),
            (exactRationalLiteral (389738012284468023) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (76891264513932161653) 38400000000000000000),
            (exactRationalLiteral (87878684425913617) 400000000000000000),
            (exactRationalLiteral (-163284771228128369) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-2274714715395364939807) 1228800000000000000000),
            (exactRationalLiteral (-73209321012967678639) 25600000000000000000),
            (exactRationalLiteral (11263368676627168193) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-127539642679164086507) 614400000000000000000),
            (exactRationalLiteral (59047666041123503701) 12800000000000000000),
            (exactRationalLiteral (-5538563012752813163) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (78529976225428332703) 102400000000000000000),
            (exactRationalLiteral (-18461781531305685191) 6400000000000000000),
            (exactRationalLiteral (1330228127148933717) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1521215558365025852387) 1228800000000000000000),
            (exactRationalLiteral (42914191138065975117) 25600000000000000000),
            (exactRationalLiteral (-2044012212709782659) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (208003787678727568959) 102400000000000000000),
            (exactRationalLiteral (-12595824426703290627) 6400000000000000000),
            (exactRationalLiteral (93071207249395929) 80000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1521215558365025852387) 1228800000000000000000),
            (exactRationalLiteral (42914191138065975117) 25600000000000000000),
            (exactRationalLiteral (-2044012212709782659) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (78529976225428332703) 102400000000000000000),
            (exactRationalLiteral (-18461781531305685191) 6400000000000000000),
            (exactRationalLiteral (1330228127148933717) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-127539642679164086507) 614400000000000000000),
            (exactRationalLiteral (59047666041123503701) 12800000000000000000),
            (exactRationalLiteral (-5538563012752813163) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2274714715395364939807) 1228800000000000000000),
            (exactRationalLiteral (-73209321012967678639) 25600000000000000000),
            (exactRationalLiteral (11263368676627168193) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (76891264513932161653) 38400000000000000000),
            (exactRationalLiteral (87878684425913617) 400000000000000000),
            (exactRationalLiteral (-163284771228128369) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-3164235346752875739) 8192000000000000000),
            (exactRationalLiteral (498974788164237467) 2560000000000000000),
            (exactRationalLiteral (389738012284468023) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-79051695181938795851) 1228800000000000000000),
            (exactRationalLiteral (346861766008219989) 25600000000000000000),
            (exactRationalLiteral (40623428435579893) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23601490398898554997) 1228800000000000000000),
            (exactRationalLiteral (28732162187955903) 5120000000000000000),
            (exactRationalLiteral (1655894543767087) 320000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-82275367469545547) 16384000000000000000),
            (exactRationalLiteral (98787902554065159) 25600000000000000000),
            (exactRationalLiteral (1573910825815047) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6208044747779847931) 1228800000000000000000),
            (exactRationalLiteral (206787030205357) 1024000000000000000),
            (exactRationalLiteral (58543977942413) 64000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2738835225385554863) 307200000000000000000),
            (exactRationalLiteral (-3821704636320407) 6400000000000000000),
            (exactRationalLiteral (-325199065284863) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (54331413681538343) 614400000000000000000),
            (exactRationalLiteral (6831258714195663) 12800000000000000000),
            (exactRationalLiteral (480681175701239) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (317187019693546313) 204800000000000000000),
            (exactRationalLiteral (10342104683727667) 12800000000000000000),
            (exactRationalLiteral (17317395836427) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (72183999174459631) 1228800000000000000000),
            (exactRationalLiteral (1524133472817471) 25600000000000000000),
            (exactRationalLiteral (-66003436493681) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-572263092148726157) 1228800000000000000000),
            (exactRationalLiteral (5046059228457299) 25600000000000000000),
            (exactRationalLiteral (456233100378163) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-853778532758574223) 1228800000000000000000),
            (exactRationalLiteral (-34913083960090079) 25600000000000000000),
            (exactRationalLiteral (-402408931779491) 320000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1258625571442147) 30720000000000000000),
            (exactRationalLiteral (14983033950749717) 3200000000000000000),
            (exactRationalLiteral (843087809560921) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-3190853424387285019) 614400000000000000000),
            (exactRationalLiteral (-62608250852975391) 2560000000000000000),
            (exactRationalLiteral (-16391925767663899) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (998909446326046951) 204800000000000000000),
            (exactRationalLiteral (1072111844000483613) 12800000000000000000),
            (exactRationalLiteral (74536749975994629) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1811386284104848849) 38400000000000000000),
            (exactRationalLiteral (-155708334881250469) 1600000000000000000),
            (exactRationalLiteral (-5176879710117391) 25000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-46139817710954943589) 614400000000000000000),
            (exactRationalLiteral (43861777659222003) 12800000000000000000),
            (exactRationalLiteral (36458056294515343) 160000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1705762185326706409) 81920000000000000000),
            (exactRationalLiteral (284181774810777483) 5120000000000000000),
            (exactRationalLiteral (-39117523004894373) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (6159126082153113) 819200000000000000),
            (exactRationalLiteral (-6159126082153113) 256000000000000000),
            (exactRationalLiteral (2053042027384371) 80000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (exactRationalLiteral (243989077426825873) 10240000000000000000),
          (exactRationalLiteral (60398381211767757) 800000000000000000),
          (exactRationalLiteral (5240278380610517) 100000000000000000),
          (exactRationalLiteral (802206745746119281) 76800000000000000000),
          (exactRationalLiteral (173799647261713481) 25600000000000000000),
          (exactRationalLiteral (3138380096629) 10000000000000000),
          (exactRationalLiteral (120452867292150983) 153600000000000000000),
          (exactRationalLiteral (71505212116231) 150000000000000000),
          (exactRationalLiteral (9580333177754023) 153600000000000000000),
          (exactRationalLiteral (122828317228672511) 76800000000000000000),
          (exactRationalLiteral (9532877225233283) 76800000000000000000),
          (exactRationalLiteral (343910211080539819) 38400000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (6434564502925491441) 3200000000000000000),
          (exactRationalLiteral (307686986034297935671) 153600000000000000000),
          (exactRationalLiteral (26181459929894569) 50000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (161918727665951221) 75000000000000000),
          (exactRationalLiteral (404348209762868497) 300000000000000000),
          (exactRationalLiteral (288142657123183861) 300000000000000000),
          (exactRationalLiteral (26181459929894569) 50000000000000000),
          (exactRationalLiteral (307686986034297935671) 153600000000000000000),
          (exactRationalLiteral (6434564502925491441) 3200000000000000000),
          (exactRationalLiteral (59469529605834751) 150000000000000000),
          (exactRationalLiteral (9761638465549931) 150000000000000000),
          (exactRationalLiteral (1172213534202457) 60000000000000000),
          (exactRationalLiteral (788834707573199) 150000000000000000),
          (exactRationalLiteral (126526661310991) 25000000000000000),
          (exactRationalLiteral (343910211080539819) 38400000000000000000),
          (exactRationalLiteral (9532877225233283) 76800000000000000000),
          (exactRationalLiteral (122828317228672511) 76800000000000000000),
          (exactRationalLiteral (9580333177754023) 153600000000000000000),
          (exactRationalLiteral (71505212116231) 150000000000000000),
          (exactRationalLiteral (120452867292150983) 153600000000000000000),
          (exactRationalLiteral (3138380096629) 10000000000000000),
          (exactRationalLiteral (173799647261713481) 25600000000000000000),
          (exactRationalLiteral (802206745746119281) 76800000000000000000),
          (exactRationalLiteral (5240278380610517) 100000000000000000),
          (exactRationalLiteral (60398381211767757) 800000000000000000),
          (exactRationalLiteral (243989077426825873) 10240000000000000000),
          (exactRationalLiteral (684347342461457) 75000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (38, 36),
      (38, 28),
      (38, 20),
      (38, 12),
      (38, 4),
      (37, 60),
      (37, 52),
      (37, 44),
      (37, 36),
      (37, 28),
      (37, 20),
      (37, 12),
      (37, 4),
      (36, 60),
      (36, 52),
      (36, 44),
      (36, 36),
      (36, 28),
      (36, 20),
      (36, 12),
      (36, 4),
      (35, 60),
      (35, 52),
      (35, 44),
      (35, 36),
      (35, 28),
      (35, 20),
      (35, 12),
      (35, 4),
      (34, 60),
      (34, 52),
      (34, 59),
      (35, 3),
      (35, 11),
      (35, 19),
      (35, 27),
      (35, 35),
      (35, 43),
      (35, 51),
      (35, 59),
      (36, 3),
      (36, 11),
      (36, 19),
      (36, 27),
      (36, 35),
      (36, 43),
      (36, 51),
      (36, 59),
      (37, 3),
      (37, 11),
      (37, 19),
      (37, 27),
      (37, 35)
    ]
    negative := ![
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      false,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true
    ]
  }
]

/-- All centered cubic, true Bernstein, center and radius checks are exact. -/
theorem generatorCoordinates18_valid : ∀ i, (generatorCoordinates18 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
