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

/-- Actual coordinate interval candidates, block 30. -/
def generatorCoordinates30 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (1) 4)
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
            (exactRationalLiteral (4835367921667552423) 1228800000000000000000),
            (exactRationalLiteral (-439578901969777493) 25600000000000000000),
            (exactRationalLiteral (39961718360888863) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (689333118019029987) 20480000000000000000),
            (exactRationalLiteral (11577804666310161) 1280000000000000000),
            (exactRationalLiteral (-8444296065242007) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-16433698088787319899) 204800000000000000000),
            (exactRationalLiteral (1373439078707363251) 12800000000000000000),
            (exactRationalLiteral (130326563495204199) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (27925089696332588593) 1228800000000000000000),
            (exactRationalLiteral (-1019146533243108023) 5120000000000000000),
            (exactRationalLiteral (-160263422135809607) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (38419636544030283383) 1228800000000000000000),
            (exactRationalLiteral (3207164754669056203) 25600000000000000000),
            (exactRationalLiteral (5688019233678863) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-962788950762459431) 76800000000000000000),
            (exactRationalLiteral (-47177635101350957) 1600000000000000000),
            (exactRationalLiteral (1921619422057933) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (506943949723929789) 204800000000000000000),
            (exactRationalLiteral (80307481964671947) 12800000000000000000),
            (exactRationalLiteral (-972392097776829) 160000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3271957297962564907) 614400000000000000000),
            (exactRationalLiteral (-70584375221749) 2560000000000000000),
            (exactRationalLiteral (1254073517722291) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (459817370566372703) 61440000000000000000),
            (exactRationalLiteral (48581944202919427) 6400000000000000000),
            (exactRationalLiteral (1245701097283963) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-12604907755182354331) 614400000000000000000),
            (exactRationalLiteral (-120903957857977111) 12800000000000000000),
            (exactRationalLiteral (-1280098770387331) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14564949238742055311) 1228800000000000000000),
            (exactRationalLiteral (-274047375858216083) 25600000000000000000),
            (exactRationalLiteral (-14055514528581767) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8697909502423014317) 614400000000000000000),
            (exactRationalLiteral (38665167127989789) 2560000000000000000),
            (exactRationalLiteral (5885351798462213) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-84504961179722857) 245760000000000000000),
            (exactRationalLiteral (-110202637330706889) 25600000000000000000),
            (exactRationalLiteral (-3384828418966997) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-563611222420883419) 204800000000000000000),
            (exactRationalLiteral (86923736462685819) 12800000000000000000),
            (exactRationalLiteral (128295234270603) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (7995440483259225731) 614400000000000000000),
            (exactRationalLiteral (-122956503255853497) 12800000000000000000),
            (exactRationalLiteral (1042797468789947) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (25736925403430093327) 614400000000000000000),
            (exactRationalLiteral (-68806553525045769) 2560000000000000000),
            (exactRationalLiteral (395661876941471) 32000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-34489652996121178361) 1228800000000000000000),
            (exactRationalLiteral (695873240059359339) 25600000000000000000),
            (exactRationalLiteral (-4967130444468109) 320000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-26225618561378245207) 1228800000000000000000),
            (exactRationalLiteral (191759537565842949) 25600000000000000000),
            (exactRationalLiteral (-235762536126223) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-328476960485177357) 61440000000000000000),
            (exactRationalLiteral (-603754416694729) 1280000000000000000),
            (exactRationalLiteral (189115603379371) 80000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-17737877359184090921) 153600000000000000000),
            (exactRationalLiteral (187630565415833541) 3200000000000000000),
            (exactRationalLiteral (-3931488677526797) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (50197013516045531387) 204800000000000000000),
            (exactRationalLiteral (-1626747058748060803) 12800000000000000000),
            (exactRationalLiteral (32152745531067801) 800000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-17737877359184090921) 153600000000000000000),
            (exactRationalLiteral (187630565415833541) 3200000000000000000),
            (exactRationalLiteral (-3931488677526797) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-328476960485177357) 61440000000000000000),
            (exactRationalLiteral (-603754416694729) 1280000000000000000),
            (exactRationalLiteral (189115603379371) 80000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-26225618561378245207) 1228800000000000000000),
            (exactRationalLiteral (191759537565842949) 25600000000000000000),
            (exactRationalLiteral (-235762536126223) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-34489652996121178361) 1228800000000000000000),
            (exactRationalLiteral (695873240059359339) 25600000000000000000),
            (exactRationalLiteral (-4967130444468109) 320000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (25736925403430093327) 614400000000000000000),
            (exactRationalLiteral (-68806553525045769) 2560000000000000000),
            (exactRationalLiteral (395661876941471) 32000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (7995440483259225731) 614400000000000000000),
            (exactRationalLiteral (-122956503255853497) 12800000000000000000),
            (exactRationalLiteral (1042797468789947) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-563611222420883419) 204800000000000000000),
            (exactRationalLiteral (86923736462685819) 12800000000000000000),
            (exactRationalLiteral (128295234270603) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-84504961179722857) 245760000000000000000),
            (exactRationalLiteral (-110202637330706889) 25600000000000000000),
            (exactRationalLiteral (-3384828418966997) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (8697909502423014317) 614400000000000000000),
            (exactRationalLiteral (38665167127989789) 2560000000000000000),
            (exactRationalLiteral (5885351798462213) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14564949238742055311) 1228800000000000000000),
            (exactRationalLiteral (-274047375858216083) 25600000000000000000),
            (exactRationalLiteral (-14055514528581767) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12604907755182354331) 614400000000000000000),
            (exactRationalLiteral (-120903957857977111) 12800000000000000000),
            (exactRationalLiteral (-1280098770387331) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (459817370566372703) 61440000000000000000),
            (exactRationalLiteral (48581944202919427) 6400000000000000000),
            (exactRationalLiteral (1245701097283963) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3271957297962564907) 614400000000000000000),
            (exactRationalLiteral (-70584375221749) 2560000000000000000),
            (exactRationalLiteral (1254073517722291) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (506943949723929789) 204800000000000000000),
            (exactRationalLiteral (80307481964671947) 12800000000000000000),
            (exactRationalLiteral (-972392097776829) 160000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-962788950762459431) 76800000000000000000),
            (exactRationalLiteral (-47177635101350957) 1600000000000000000),
            (exactRationalLiteral (1921619422057933) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (38419636544030283383) 1228800000000000000000),
            (exactRationalLiteral (3207164754669056203) 25600000000000000000),
            (exactRationalLiteral (5688019233678863) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (27925089696332588593) 1228800000000000000000),
            (exactRationalLiteral (-1019146533243108023) 5120000000000000000),
            (exactRationalLiteral (-160263422135809607) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16433698088787319899) 204800000000000000000),
            (exactRationalLiteral (1373439078707363251) 12800000000000000000),
            (exactRationalLiteral (130326563495204199) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (689333118019029987) 20480000000000000000),
            (exactRationalLiteral (11577804666310161) 1280000000000000000),
            (exactRationalLiteral (-8444296065242007) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (4835367921667552423) 1228800000000000000000),
            (exactRationalLiteral (-439578901969777493) 25600000000000000000),
            (exactRationalLiteral (39961718360888863) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (32695951386181797) 6400000000000000000),
          (exactRationalLiteral (65218125697223677) 1920000000000000000),
          (exactRationalLiteral (55214453694390111) 640000000000000000),
          (exactRationalLiteral (222240998353277563) 6400000000000000000),
          (exactRationalLiteral (1200370425930459037) 30720000000000000000),
          (exactRationalLiteral (34294923874162469) 2400000000000000000),
          (exactRationalLiteral (72695000421274811) 25600000000000000000),
          (exactRationalLiteral (51187784528156153) 9600000000000000000),
          (exactRationalLiteral (102019852939927473) 12800000000000000000),
          (exactRationalLiteral (1621374745901993953) 76800000000000000000),
          (exactRationalLiteral (1928904774969587921) 153600000000000000000),
          (exactRationalLiteral (1161974333717900311) 76800000000000000000),
          (exactRationalLiteral (95194525269106843) 153600000000000000000),
          (exactRationalLiteral (30452011668187151) 9600000000000000000),
          (exactRationalLiteral (130738417240780631) 9600000000000000000),
          (exactRationalLiteral (418738037644792799) 9600000000000000000),
          (exactRationalLiteral (190902261792577523) 6400000000000000000),
          (exactRationalLiteral (139590504331277661) 6400000000000000000),
          (exactRationalLiteral (206083377616563943) 38400000000000000000),
          (exactRationalLiteral (190757555586803863) 1600000000000000000),
          (exactRationalLiteral (2430765386427549413) 9600000000000000000),
          (exactRationalLiteral (190757555586803863) 1600000000000000000),
          (exactRationalLiteral (206083377616563943) 38400000000000000000),
          (exactRationalLiteral (139590504331277661) 6400000000000000000),
          (exactRationalLiteral (190902261792577523) 6400000000000000000),
          (exactRationalLiteral (418738037644792799) 9600000000000000000),
          (exactRationalLiteral (130738417240780631) 9600000000000000000),
          (exactRationalLiteral (30452011668187151) 9600000000000000000),
          (exactRationalLiteral (95194525269106843) 153600000000000000000),
          (exactRationalLiteral (1161974333717900311) 76800000000000000000),
          (exactRationalLiteral (1928904774969587921) 153600000000000000000),
          (exactRationalLiteral (1621374745901993953) 76800000000000000000),
          (exactRationalLiteral (102019852939927473) 12800000000000000000),
          (exactRationalLiteral (51187784528156153) 9600000000000000000),
          (exactRationalLiteral (72695000421274811) 25600000000000000000),
          (exactRationalLiteral (34294923874162469) 2400000000000000000),
          (exactRationalLiteral (1200370425930459037) 30720000000000000000),
          (exactRationalLiteral (222240998353277563) 6400000000000000000),
          (exactRationalLiteral (55214453694390111) 640000000000000000),
          (exactRationalLiteral (65218125697223677) 1920000000000000000),
          (exactRationalLiteral (32695951386181797) 6400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (38, 62),
      (38, 54),
      (38, 46),
      (38, 38),
      (38, 30),
      (38, 22),
      (38, 14),
      (38, 6),
      (37, 62),
      (37, 54),
      (37, 46),
      (37, 38),
      (37, 30),
      (37, 22),
      (37, 14),
      (37, 6),
      (36, 62),
      (36, 54),
      (36, 46),
      (36, 38),
      (36, 30),
      (36, 22),
      (36, 14),
      (36, 6),
      (35, 62),
      (35, 54),
      (35, 46),
      (35, 38),
      (35, 30),
      (35, 22),
      (35, 14),
      (35, 6),
      (34, 62),
      (34, 54),
      (34, 57),
      (35, 1),
      (35, 9),
      (35, 17),
      (35, 25),
      (35, 33),
      (35, 41),
      (35, 49),
      (35, 57),
      (36, 1),
      (36, 9),
      (36, 17),
      (36, 25),
      (36, 33),
      (36, 41),
      (36, 49),
      (36, 57),
      (37, 1),
      (37, 9)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (3) 8)
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
            (exactRationalLiteral (882790687426908519) 409600000000000000000),
            (exactRationalLiteral (-294263562475636173) 25600000000000000000),
            (exactRationalLiteral (32695951386181797) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2044466089091922563) 61440000000000000000),
            (exactRationalLiteral (-18033649684720007) 1280000000000000000),
            (exactRationalLiteral (-6361431110273077) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-13230997051748924049) 204800000000000000000),
            (exactRationalLiteral (14372162169219671) 102400000000000000),
            (exactRationalLiteral (81214032727343613) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1360887136216821071) 409600000000000000000),
            (exactRationalLiteral (-5491883375788826459) 25600000000000000000),
            (exactRationalLiteral (-7562386530166713) 320000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (19127952891562583383) 409600000000000000000),
            (exactRationalLiteral (3056405517523263251) 25600000000000000000),
            (exactRationalLiteral (-81067637806575339) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-404613285896251339) 25600000000000000000),
            (exactRationalLiteral (-7002684420912249) 320000000000000000),
            (exactRationalLiteral (4160487076336923) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (641475329061584279) 204800000000000000000),
            (exactRationalLiteral (50906026054906131) 12800000000000000000),
            (exactRationalLiteral (-9838767465998763) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3290969243655093713) 614400000000000000000),
            (exactRationalLiteral (7703669563037311) 12800000000000000000),
            (exactRationalLiteral (2774222201850737) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2604780385823072969) 307200000000000000000),
            (exactRationalLiteral (53191475895197947) 6400000000000000000),
            (exactRationalLiteral (1059064748855297) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-889466468317526447) 40960000000000000000),
            (exactRationalLiteral (-124176521533542303) 12800000000000000000),
            (exactRationalLiteral (-71236613479053) 160000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5464580662356123023) 409600000000000000000),
            (exactRationalLiteral (-338190593389561179) 25600000000000000000),
            (exactRationalLiteral (-18016094237090781) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9930501577883892119) 614400000000000000000),
            (exactRationalLiteral (43574732570723317) 2560000000000000000),
            (exactRationalLiteral (6388561808371607) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1110510562952209991) 1228800000000000000000),
            (exactRationalLiteral (-116817947027450081) 25600000000000000000),
            (exactRationalLiteral (77173570595401) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1167607145411667203) 614400000000000000000),
            (exactRationalLiteral (86482835657413859) 12800000000000000000),
            (exactRationalLiteral (-172385314797799) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1454330497907029909) 122880000000000000000),
            (exactRationalLiteral (-118066585287910993) 12800000000000000000),
            (exactRationalLiteral (280432303036261) 160000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (4757427772647673993) 122880000000000000000),
            (exactRationalLiteral (-306610828692477541) 12800000000000000000),
            (exactRationalLiteral (8819422542838877) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-10200268217588085881) 409600000000000000000),
            (exactRationalLiteral (602348996004422771) 25600000000000000000),
            (exactRationalLiteral (-21926469805127739) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8359903842349145559) 409600000000000000000),
            (exactRationalLiteral (189905967105970813) 25600000000000000000),
            (exactRationalLiteral (-138204538761969) 320000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-549883863059707169) 102400000000000000000),
            (exactRationalLiteral (512994756536219) 6400000000000000000),
            (exactRationalLiteral (820305403108077) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1110531820791161329) 10240000000000000000),
            (exactRationalLiteral (34510374036344401) 640000000000000000),
            (exactRationalLiteral (-3607858939528971) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (141206432978907583283) 614400000000000000000),
            (exactRationalLiteral (-300623031636103887) 2560000000000000000),
            (exactRationalLiteral (29663204752702883) 800000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1110531820791161329) 10240000000000000000),
            (exactRationalLiteral (34510374036344401) 640000000000000000),
            (exactRationalLiteral (-3607858939528971) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-549883863059707169) 102400000000000000000),
            (exactRationalLiteral (512994756536219) 6400000000000000000),
            (exactRationalLiteral (820305403108077) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-8359903842349145559) 409600000000000000000),
            (exactRationalLiteral (189905967105970813) 25600000000000000000),
            (exactRationalLiteral (-138204538761969) 320000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10200268217588085881) 409600000000000000000),
            (exactRationalLiteral (602348996004422771) 25600000000000000000),
            (exactRationalLiteral (-21926469805127739) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4757427772647673993) 122880000000000000000),
            (exactRationalLiteral (-306610828692477541) 12800000000000000000),
            (exactRationalLiteral (8819422542838877) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1454330497907029909) 122880000000000000000),
            (exactRationalLiteral (-118066585287910993) 12800000000000000000),
            (exactRationalLiteral (280432303036261) 160000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1167607145411667203) 614400000000000000000),
            (exactRationalLiteral (86482835657413859) 12800000000000000000),
            (exactRationalLiteral (-172385314797799) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1110510562952209991) 1228800000000000000000),
            (exactRationalLiteral (-116817947027450081) 25600000000000000000),
            (exactRationalLiteral (77173570595401) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (9930501577883892119) 614400000000000000000),
            (exactRationalLiteral (43574732570723317) 2560000000000000000),
            (exactRationalLiteral (6388561808371607) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-5464580662356123023) 409600000000000000000),
            (exactRationalLiteral (-338190593389561179) 25600000000000000000),
            (exactRationalLiteral (-18016094237090781) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-889466468317526447) 40960000000000000000),
            (exactRationalLiteral (-124176521533542303) 12800000000000000000),
            (exactRationalLiteral (-71236613479053) 160000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2604780385823072969) 307200000000000000000),
            (exactRationalLiteral (53191475895197947) 6400000000000000000),
            (exactRationalLiteral (1059064748855297) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3290969243655093713) 614400000000000000000),
            (exactRationalLiteral (7703669563037311) 12800000000000000000),
            (exactRationalLiteral (2774222201850737) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (641475329061584279) 204800000000000000000),
            (exactRationalLiteral (50906026054906131) 12800000000000000000),
            (exactRationalLiteral (-9838767465998763) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-404613285896251339) 25600000000000000000),
            (exactRationalLiteral (-7002684420912249) 320000000000000000),
            (exactRationalLiteral (4160487076336923) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (19127952891562583383) 409600000000000000000),
            (exactRationalLiteral (3056405517523263251) 25600000000000000000),
            (exactRationalLiteral (-81067637806575339) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1360887136216821071) 409600000000000000000),
            (exactRationalLiteral (-5491883375788826459) 25600000000000000000),
            (exactRationalLiteral (-7562386530166713) 320000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13230997051748924049) 204800000000000000000),
            (exactRationalLiteral (14372162169219671) 102400000000000000),
            (exactRationalLiteral (81214032727343613) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2044466089091922563) 61440000000000000000),
            (exactRationalLiteral (-18033649684720007) 1280000000000000000),
            (exactRationalLiteral (-6361431110273077) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (882790687426908519) 409600000000000000000),
            (exactRationalLiteral (-294263562475636173) 25600000000000000000),
            (exactRationalLiteral (32695951386181797) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (3632883487353533) 1228800000000000000),
          (exactRationalLiteral (259805164042222361) 7680000000000000000),
          (exactRationalLiteral (373452946709484897) 5120000000000000000),
          (exactRationalLiteral (40254924978958897) 2400000000000000000),
          (exactRationalLiteral (129426747041636107) 2400000000000000000),
          (exactRationalLiteral (10197493976142871) 600000000000000000),
          (exactRationalLiteral (1331470937150337) 400000000000000000),
          (exactRationalLiteral (649055272127309) 120000000000000000),
          (exactRationalLiteral (10810307381175853) 1200000000000000000),
          (exactRationalLiteral (1674210593348903) 75000000000000000),
          (exactRationalLiteral (34110043632426913) 2400000000000000000),
          (exactRationalLiteral (2588754847869827) 150000000000000000),
          (exactRationalLiteral (2849613051421861) 2400000000000000000),
          (exactRationalLiteral (35722243268330119) 15360000000000000000),
          (exactRationalLiteral (190746976198030769) 15360000000000000000),
          (exactRationalLiteral (3091745709891833521) 76800000000000000000),
          (exactRationalLiteral (4059385705175189447) 153600000000000000000),
          (exactRationalLiteral (641281871659198421) 30720000000000000000),
          (exactRationalLiteral (17198411725475627) 3200000000000000000),
          (exactRationalLiteral (16783806947363449) 150000000000000000),
          (exactRationalLiteral (18225751604762054087) 76800000000000000000),
          (exactRationalLiteral (16783806947363449) 150000000000000000),
          (exactRationalLiteral (17198411725475627) 3200000000000000000),
          (exactRationalLiteral (641281871659198421) 30720000000000000000),
          (exactRationalLiteral (4059385705175189447) 153600000000000000000),
          (exactRationalLiteral (3091745709891833521) 76800000000000000000),
          (exactRationalLiteral (190746976198030769) 15360000000000000000),
          (exactRationalLiteral (35722243268330119) 15360000000000000000),
          (exactRationalLiteral (2849613051421861) 2400000000000000000),
          (exactRationalLiteral (2588754847869827) 150000000000000000),
          (exactRationalLiteral (34110043632426913) 2400000000000000000),
          (exactRationalLiteral (1674210593348903) 75000000000000000),
          (exactRationalLiteral (10810307381175853) 1200000000000000000),
          (exactRationalLiteral (649055272127309) 120000000000000000),
          (exactRationalLiteral (1331470937150337) 400000000000000000),
          (exactRationalLiteral (10197493976142871) 600000000000000000),
          (exactRationalLiteral (129426747041636107) 2400000000000000000),
          (exactRationalLiteral (40254924978958897) 2400000000000000000),
          (exactRationalLiteral (373452946709484897) 5120000000000000000),
          (exactRationalLiteral (259805164042222361) 7680000000000000000),
          (exactRationalLiteral (3632883487353533) 1228800000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (38, 63),
      (38, 55),
      (38, 47),
      (38, 39),
      (38, 31),
      (38, 23),
      (38, 15),
      (38, 7),
      (37, 63),
      (37, 55),
      (37, 47),
      (37, 39),
      (37, 31),
      (37, 23),
      (37, 15),
      (37, 7),
      (36, 63),
      (36, 55),
      (36, 47),
      (36, 39),
      (36, 31),
      (36, 23),
      (36, 15),
      (36, 7),
      (35, 63),
      (35, 55),
      (35, 47),
      (35, 39),
      (35, 31),
      (35, 23),
      (35, 15),
      (35, 7),
      (34, 63),
      (34, 55),
      (34, 56),
      (35, 0),
      (35, 8),
      (35, 16),
      (35, 24),
      (35, 32),
      (35, 40),
      (35, 48),
      (35, 56),
      (36, 0),
      (36, 8),
      (36, 16),
      (36, 24),
      (36, 32),
      (36, 40),
      (36, 48),
      (36, 56),
      (37, 0),
      (37, 8)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (1) 2)
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
            (exactRationalLiteral (1246079036162261819) 1228800000000000000000),
            (exactRationalLiteral (-178011290880323117) 25600000000000000000),
            (exactRationalLiteral (25430184411474731) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1868258477480201317) 61440000000000000000),
            (exactRationalLiteral (-7862728843174891) 256000000000000000),
            (exactRationalLiteral (-4278566155304147) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-1875716750578355859) 40960000000000000000),
            (exactRationalLiteral (404630268105222431) 2560000000000000000),
            (exactRationalLiteral (32101501959483027) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-36997898897253520579) 1228800000000000000000),
            (exactRationalLiteral (-1079645625484441727) 5120000000000000000),
            (exactRationalLiteral (84639556834142477) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (74402457497987408779) 1228800000000000000000),
            (exactRationalLiteral (2558623652216453491) 25600000000000000000),
            (exactRationalLiteral (-167823294846829541) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1365039074782962451) 76800000000000000000),
            (exactRationalLiteral (-13893738490655573) 1600000000000000000),
            (exactRationalLiteral (6399354730615913) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (139459313734249733) 40960000000000000000),
            (exactRationalLiteral (1597342236681843) 12800000000000000000),
            (exactRationalLiteral (-14815574443113381) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1125520840730680069) 204800000000000000000),
            (exactRationalLiteral (21840855738697151) 12800000000000000000),
            (exactRationalLiteral (4294370885979183) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (978630490928936517) 102400000000000000000),
            (exactRationalLiteral (57054462193761803) 6400000000000000000),
            (exactRationalLiteral (872428400426631) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-14087634687960925439) 614400000000000000000),
            (exactRationalLiteral (-123753422397139231) 12800000000000000000),
            (exactRationalLiteral (567732635596801) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-18654920997084861571) 1228800000000000000000),
            (exactRationalLiteral (-418176129754942331) 25600000000000000000),
            (exactRationalLiteral (-4395334789119959) 320000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11316419136745688489) 614400000000000000000),
            (exactRationalLiteral (244434330106921801) 12800000000000000000),
            (exactRationalLiteral (6891771818281001) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1796644154311516073) 1228800000000000000000),
            (exactRationalLiteral (-109585248765943681) 25600000000000000000),
            (exactRationalLiteral (3539175560157799) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-665066861336420029) 614400000000000000000),
            (exactRationalLiteral (80028323870773859) 12800000000000000000),
            (exactRationalLiteral (-473065863866201) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (6581516372175424679) 614400000000000000000),
            (exactRationalLiteral (-111739211134403057) 12800000000000000000),
            (exactRationalLiteral (1761525561572663) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (22049018464074779651) 614400000000000000000),
            (exactRationalLiteral (-273477387282517829) 12800000000000000000),
            (exactRationalLiteral (7747298162140979) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-27238191584730402661) 1228800000000000000000),
            (exactRationalLiteral (520461481618337427) 25600000000000000000),
            (exactRationalLiteral (-19017287387914933) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23950389037368064427) 1228800000000000000000),
            (exactRationalLiteral (186231356015364189) 25600000000000000000),
            (exactRationalLiteral (-1146282851493467) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1637231046257762381) 307200000000000000000),
            (exactRationalLiteral (3543671141390971) 6400000000000000000),
            (exactRationalLiteral (695032789319299) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-15664665879099444253) 153600000000000000000),
            (exactRationalLiteral (158767693899601773) 3200000000000000000),
            (exactRationalLiteral (-656845840306229) 40000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (132533742323743441597) 614400000000000000000),
            (exactRationalLiteral (-1389441420726437739) 12800000000000000000),
            (exactRationalLiteral (5434732794867593) 160000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-15664665879099444253) 153600000000000000000),
            (exactRationalLiteral (158767693899601773) 3200000000000000000),
            (exactRationalLiteral (-656845840306229) 40000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1637231046257762381) 307200000000000000000),
            (exactRationalLiteral (3543671141390971) 6400000000000000000),
            (exactRationalLiteral (695032789319299) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-23950389037368064427) 1228800000000000000000),
            (exactRationalLiteral (186231356015364189) 25600000000000000000),
            (exactRationalLiteral (-1146282851493467) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-27238191584730402661) 1228800000000000000000),
            (exactRationalLiteral (520461481618337427) 25600000000000000000),
            (exactRationalLiteral (-19017287387914933) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22049018464074779651) 614400000000000000000),
            (exactRationalLiteral (-273477387282517829) 12800000000000000000),
            (exactRationalLiteral (7747298162140979) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (6581516372175424679) 614400000000000000000),
            (exactRationalLiteral (-111739211134403057) 12800000000000000000),
            (exactRationalLiteral (1761525561572663) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-665066861336420029) 614400000000000000000),
            (exactRationalLiteral (80028323870773859) 12800000000000000000),
            (exactRationalLiteral (-473065863866201) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1796644154311516073) 1228800000000000000000),
            (exactRationalLiteral (-109585248765943681) 25600000000000000000),
            (exactRationalLiteral (3539175560157799) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (11316419136745688489) 614400000000000000000),
            (exactRationalLiteral (244434330106921801) 12800000000000000000),
            (exactRationalLiteral (6891771818281001) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-18654920997084861571) 1228800000000000000000),
            (exactRationalLiteral (-418176129754942331) 25600000000000000000),
            (exactRationalLiteral (-4395334789119959) 320000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14087634687960925439) 614400000000000000000),
            (exactRationalLiteral (-123753422397139231) 12800000000000000000),
            (exactRationalLiteral (567732635596801) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (978630490928936517) 102400000000000000000),
            (exactRationalLiteral (57054462193761803) 6400000000000000000),
            (exactRationalLiteral (872428400426631) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1125520840730680069) 204800000000000000000),
            (exactRationalLiteral (21840855738697151) 12800000000000000000),
            (exactRationalLiteral (4294370885979183) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (139459313734249733) 40960000000000000000),
            (exactRationalLiteral (1597342236681843) 12800000000000000000),
            (exactRationalLiteral (-14815574443113381) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1365039074782962451) 76800000000000000000),
            (exactRationalLiteral (-13893738490655573) 1600000000000000000),
            (exactRationalLiteral (6399354730615913) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (74402457497987408779) 1228800000000000000000),
            (exactRationalLiteral (2558623652216453491) 25600000000000000000),
            (exactRationalLiteral (-167823294846829541) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-36997898897253520579) 1228800000000000000000),
            (exactRationalLiteral (-1079645625484441727) 5120000000000000000),
            (exactRationalLiteral (84639556834142477) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1875716750578355859) 40960000000000000000),
            (exactRationalLiteral (404630268105222431) 2560000000000000000),
            (exactRationalLiteral (32101501959483027) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1868258477480201317) 61440000000000000000),
            (exactRationalLiteral (-7862728843174891) 256000000000000000),
            (exactRationalLiteral (-4278566155304147) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (1246079036162261819) 1228800000000000000000),
            (exactRationalLiteral (-178011290880323117) 25600000000000000000),
            (exactRationalLiteral (25430184411474731) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (3632883487353533) 2400000000000000000),
          (exactRationalLiteral (2568127967688057) 80000000000000000),
          (exactRationalLiteral (22190328456374541) 400000000000000000),
          (exactRationalLiteral (2203226619344801293) 51200000000000000000),
          (exactRationalLiteral (3397145030899006397) 51200000000000000000),
          (exactRationalLiteral (57768816742973893) 3200000000000000000),
          (exactRationalLiteral (21987406522730193) 6400000000000000000),
          (exactRationalLiteral (431966034551016679) 76800000000000000000),
          (exactRationalLiteral (77739470659879013) 7680000000000000000),
          (exactRationalLiteral (602363741641419029) 25600000000000000000),
          (exactRationalLiteral (832389987418364269) 51200000000000000000),
          (exactRationalLiteral (1508831130940781449) 76800000000000000000),
          (exactRationalLiteral (52826284323352313) 30720000000000000000),
          (exactRationalLiteral (74177744102707) 50000000000000000),
          (exactRationalLiteral (2703843320406311) 240000000000000000),
          (exactRationalLiteral (44713337075388877) 1200000000000000000),
          (exactRationalLiteral (56363442349526887) 2400000000000000000),
          (exactRationalLiteral (47875574851347257) 2400000000000000000),
          (exactRationalLiteral (3214285791029459) 600000000000000000),
          (exactRationalLiteral (25235911661362253) 240000000000000000),
          (exactRationalLiteral (89052625226715463) 400000000000000000),
          (exactRationalLiteral (25235911661362253) 240000000000000000),
          (exactRationalLiteral (3214285791029459) 600000000000000000),
          (exactRationalLiteral (47875574851347257) 2400000000000000000),
          (exactRationalLiteral (56363442349526887) 2400000000000000000),
          (exactRationalLiteral (44713337075388877) 1200000000000000000),
          (exactRationalLiteral (2703843320406311) 240000000000000000),
          (exactRationalLiteral (74177744102707) 50000000000000000),
          (exactRationalLiteral (52826284323352313) 30720000000000000000),
          (exactRationalLiteral (1508831130940781449) 76800000000000000000),
          (exactRationalLiteral (832389987418364269) 51200000000000000000),
          (exactRationalLiteral (602363741641419029) 25600000000000000000),
          (exactRationalLiteral (77739470659879013) 7680000000000000000),
          (exactRationalLiteral (431966034551016679) 76800000000000000000),
          (exactRationalLiteral (21987406522730193) 6400000000000000000),
          (exactRationalLiteral (57768816742973893) 3200000000000000000),
          (exactRationalLiteral (3397145030899006397) 51200000000000000000),
          (exactRationalLiteral (2203226619344801293) 51200000000000000000),
          (exactRationalLiteral (22190328456374541) 400000000000000000),
          (exactRationalLiteral (2568127967688057) 80000000000000000),
          (exactRationalLiteral (3632883487353533) 2400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (39, 0),
      (38, 56),
      (38, 48),
      (38, 40),
      (38, 32),
      (38, 24),
      (38, 16),
      (38, 8),
      (38, 0),
      (37, 56),
      (37, 48),
      (37, 40),
      (37, 32),
      (37, 24),
      (37, 16),
      (37, 8),
      (37, 0),
      (36, 56),
      (36, 48),
      (36, 40),
      (36, 32),
      (36, 24),
      (36, 16),
      (36, 8),
      (36, 0),
      (35, 56),
      (35, 48),
      (35, 40),
      (35, 32),
      (35, 24),
      (35, 16),
      (35, 8),
      (35, 0),
      (34, 56),
      (34, 55),
      (34, 63),
      (35, 7),
      (35, 15),
      (35, 23),
      (35, 31),
      (35, 39),
      (35, 47),
      (35, 55),
      (35, 63),
      (36, 7),
      (36, 15),
      (36, 23),
      (36, 31),
      (36, 39),
      (36, 47),
      (36, 55),
      (36, 63),
      (37, 7)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (5) 8)
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
            (exactRationalLiteral (3632883487353533) 9830400000000000000),
            (exactRationalLiteral (-3632883487353533) 1024000000000000000),
            (exactRationalLiteral (3632883487353533) 320000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (529788426047060181) 20480000000000000000),
            (exactRationalLiteral (-52262178927153183) 1280000000000000000),
            (exactRationalLiteral (-2195701200335217) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-210774337534350813) 8192000000000000000),
            (exactRationalLiteral (2053332286828323091) 12800000000000000000),
            (exactRationalLiteral (-17011028808377559) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-67881787021837158497) 1228800000000000000000),
            (exactRationalLiteral (-4814766921115686643) 25600000000000000000),
            (exactRationalLiteral (207091046319118519) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3495731889798526337) 49152000000000000000),
            (exactRationalLiteral (1713819158748626923) 25600000000000000000),
            (exactRationalLiteral (-254578951887083743) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1362653778342388973) 76800000000000000000),
            (exactRationalLiteral (16181415740366059) 1600000000000000000),
            (exactRationalLiteral (8638222384894903) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (634593212736006003) 204800000000000000000),
            (exactRationalLiteral (-67618569490000917) 12800000000000000000),
            (exactRationalLiteral (-19792381420227999) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3565220701992487093) 614400000000000000000),
            (exactRationalLiteral (1682345466034831) 512000000000000000),
            (exactRationalLiteral (5814519570107629) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3287940841360785277) 307200000000000000000),
            (exactRationalLiteral (12034180619722199) 1280000000000000000),
            (exactRationalLiteral (137158410399593) 80000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-14819646767904630949) 614400000000000000000),
            (exactRationalLiteral (-23926932089753579) 2560000000000000000),
            (exactRationalLiteral (1491648338588867) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-21443540181795749153) 1228800000000000000000),
            (exactRationalLiteral (-514003984954359539) 25600000000000000000),
            (exactRationalLiteral (-25937253654108809) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12867739219246228883) 614400000000000000000),
            (exactRationalLiteral (273007837399864593) 12800000000000000000),
            (exactRationalLiteral (1478996365638079) 160000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2397837532227034979) 1228800000000000000000),
            (exactRationalLiteral (-88504542546187689) 25600000000000000000),
            (exactRationalLiteral (7001177549720197) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2923926412334893) 8192000000000000000),
            (exactRationalLiteral (67560201102765819) 12800000000000000000),
            (exactRationalLiteral (-773746412934603) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (237346274731737749) 24576000000000000000),
            (exactRationalLiteral (-103974380795329689) 12800000000000000000),
            (exactRationalLiteral (2120889607964021) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (20496833220802572833) 614400000000000000000),
            (exactRationalLiteral (-244632443395349709) 12800000000000000000),
            (exactRationalLiteral (6675173781443081) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-24331993414006506071) 1228800000000000000000),
            (exactRationalLiteral (450210696901103307) 25600000000000000000),
            (exactRationalLiteral (-16108104970702127) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4569715467224907077) 245760000000000000000),
            (exactRationalLiteral (180735704294023077) 25600000000000000000),
            (exactRationalLiteral (-1601543009177089) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1608129716392740079) 307200000000000000000),
            (exactRationalLiteral (6073257071090611) 6400000000000000000),
            (exactRationalLiteral (569760175530521) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-14750175947168216051) 153600000000000000000),
            (exactRationalLiteral (29255607313894569) 640000000000000000),
            (exactRationalLiteral (-2960599463533319) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (41504406534654470357) 204800000000000000000),
            (exactRationalLiteral (-257145169277163143) 2560000000000000000),
            (exactRationalLiteral (24684123195973047) 800000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14750175947168216051) 153600000000000000000),
            (exactRationalLiteral (29255607313894569) 640000000000000000),
            (exactRationalLiteral (-2960599463533319) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1608129716392740079) 307200000000000000000),
            (exactRationalLiteral (6073257071090611) 6400000000000000000),
            (exactRationalLiteral (569760175530521) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4569715467224907077) 245760000000000000000),
            (exactRationalLiteral (180735704294023077) 25600000000000000000),
            (exactRationalLiteral (-1601543009177089) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24331993414006506071) 1228800000000000000000),
            (exactRationalLiteral (450210696901103307) 25600000000000000000),
            (exactRationalLiteral (-16108104970702127) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (20496833220802572833) 614400000000000000000),
            (exactRationalLiteral (-244632443395349709) 12800000000000000000),
            (exactRationalLiteral (6675173781443081) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (237346274731737749) 24576000000000000000),
            (exactRationalLiteral (-103974380795329689) 12800000000000000000),
            (exactRationalLiteral (2120889607964021) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2923926412334893) 8192000000000000000),
            (exactRationalLiteral (67560201102765819) 12800000000000000000),
            (exactRationalLiteral (-773746412934603) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2397837532227034979) 1228800000000000000000),
            (exactRationalLiteral (-88504542546187689) 25600000000000000000),
            (exactRationalLiteral (7001177549720197) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (12867739219246228883) 614400000000000000000),
            (exactRationalLiteral (273007837399864593) 12800000000000000000),
            (exactRationalLiteral (1478996365638079) 160000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-21443540181795749153) 1228800000000000000000),
            (exactRationalLiteral (-514003984954359539) 25600000000000000000),
            (exactRationalLiteral (-25937253654108809) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14819646767904630949) 614400000000000000000),
            (exactRationalLiteral (-23926932089753579) 2560000000000000000),
            (exactRationalLiteral (1491648338588867) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3287940841360785277) 307200000000000000000),
            (exactRationalLiteral (12034180619722199) 1280000000000000000),
            (exactRationalLiteral (137158410399593) 80000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3565220701992487093) 614400000000000000000),
            (exactRationalLiteral (1682345466034831) 512000000000000000),
            (exactRationalLiteral (5814519570107629) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (634593212736006003) 204800000000000000000),
            (exactRationalLiteral (-67618569490000917) 12800000000000000000),
            (exactRationalLiteral (-19792381420227999) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1362653778342388973) 76800000000000000000),
            (exactRationalLiteral (16181415740366059) 1600000000000000000),
            (exactRationalLiteral (8638222384894903) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (3495731889798526337) 49152000000000000000),
            (exactRationalLiteral (1713819158748626923) 25600000000000000000),
            (exactRationalLiteral (-254578951887083743) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-67881787021837158497) 1228800000000000000000),
            (exactRationalLiteral (-4814766921115686643) 25600000000000000000),
            (exactRationalLiteral (207091046319118519) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-210774337534350813) 8192000000000000000),
            (exactRationalLiteral (2053332286828323091) 12800000000000000000),
            (exactRationalLiteral (-17011028808377559) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (529788426047060181) 20480000000000000000),
            (exactRationalLiteral (-52262178927153183) 1280000000000000000),
            (exactRationalLiteral (-2195701200335217) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 9830400000000000000),
            (exactRationalLiteral (-3632883487353533) 1024000000000000000),
            (exactRationalLiteral (3632883487353533) 320000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (32695951386181797) 51200000000000000000),
          (exactRationalLiteral (217315409855518747) 7680000000000000000),
          (exactRationalLiteral (916439541525103443) 25600000000000000000),
          (exactRationalLiteral (1275681076585693357) 19200000000000000000),
          (exactRationalLiteral (1433244375578557201) 19200000000000000000),
          (exactRationalLiteral (28883391504915457) 1600000000000000000),
          (exactRationalLiteral (85406108579412253) 25600000000000000000),
          (exactRationalLiteral (19320834609361909) 3200000000000000000),
          (exactRationalLiteral (9037545855829161) 800000000000000000),
          (exactRationalLiteral (1896701730797959) 76800000000000000),
          (exactRationalLiteral (360396002929303261) 19200000000000000000),
          (exactRationalLiteral (214206238780239821) 9600000000000000000),
          (exactRationalLiteral (41259634784713379) 19200000000000000000),
          (exactRationalLiteral (54103697381845309) 76800000000000000000),
          (exactRationalLiteral (781470374685016147) 76800000000000000000),
          (exactRationalLiteral (2656411516815412519) 76800000000000000000),
          (exactRationalLiteral (1072183517117938699) 51200000000000000000),
          (exactRationalLiteral (974806726998137253) 51200000000000000000),
          (exactRationalLiteral (13538146423104383) 2560000000000000000),
          (exactRationalLiteral (316626118127838197) 3200000000000000000),
          (exactRationalLiteral (16055711785387244977) 76800000000000000000),
          (exactRationalLiteral (316626118127838197) 3200000000000000000),
          (exactRationalLiteral (13538146423104383) 2560000000000000000),
          (exactRationalLiteral (974806726998137253) 51200000000000000000),
          (exactRationalLiteral (1072183517117938699) 51200000000000000000),
          (exactRationalLiteral (2656411516815412519) 76800000000000000000),
          (exactRationalLiteral (781470374685016147) 76800000000000000000),
          (exactRationalLiteral (54103697381845309) 76800000000000000000),
          (exactRationalLiteral (41259634784713379) 19200000000000000000),
          (exactRationalLiteral (214206238780239821) 9600000000000000000),
          (exactRationalLiteral (360396002929303261) 19200000000000000000),
          (exactRationalLiteral (1896701730797959) 76800000000000000),
          (exactRationalLiteral (9037545855829161) 800000000000000000),
          (exactRationalLiteral (19320834609361909) 3200000000000000000),
          (exactRationalLiteral (85406108579412253) 25600000000000000000),
          (exactRationalLiteral (28883391504915457) 1600000000000000000),
          (exactRationalLiteral (1433244375578557201) 19200000000000000000),
          (exactRationalLiteral (1275681076585693357) 19200000000000000000),
          (exactRationalLiteral (916439541525103443) 25600000000000000000),
          (exactRationalLiteral (217315409855518747) 7680000000000000000),
          (exactRationalLiteral (32695951386181797) 51200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (39, 1),
      (38, 57),
      (38, 49),
      (38, 41),
      (38, 33),
      (38, 25),
      (38, 17),
      (38, 9),
      (38, 1),
      (37, 57),
      (37, 49),
      (37, 41),
      (37, 33),
      (37, 25),
      (37, 17),
      (37, 9),
      (37, 1),
      (36, 57),
      (36, 49),
      (36, 41),
      (36, 33),
      (36, 25),
      (36, 17),
      (36, 9),
      (36, 1),
      (35, 57),
      (35, 49),
      (35, 41),
      (35, 33),
      (35, 25),
      (35, 17),
      (35, 9),
      (35, 1),
      (34, 57),
      (34, 54),
      (34, 62),
      (35, 6),
      (35, 14),
      (35, 22),
      (35, 30),
      (35, 38),
      (35, 46),
      (35, 54),
      (35, 62),
      (36, 6),
      (36, 14),
      (36, 22),
      (36, 30),
      (36, 38),
      (36, 46),
      (36, 54),
      (36, 62),
      (37, 6)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (3) 4)
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
            (exactRationalLiteral (32695951386181797) 409600000000000000000),
            (exactRationalLiteral (-32695951386181797) 25600000000000000000),
            (exactRationalLiteral (10898650462060599) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1257775249994114561) 61440000000000000000),
            (exactRationalLiteral (-56879253818556191) 1280000000000000000),
            (exactRationalLiteral (-112836245366287) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-1296221354292781827) 204800000000000000000),
            (exactRationalLiteral (1887063110059091683) 12800000000000000000),
            (exactRationalLiteral (-13224711915247629) 160000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-31265163344920650653) 409600000000000000000),
            (exactRationalLiteral (-3741499756869260483) 25600000000000000000),
            (exactRationalLiteral (329542535804094561) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (31424747382216299413) 409600000000000000000),
            (exactRationalLiteral (521992037119783547) 25600000000000000000),
            (exactRationalLiteral (-68266921785467589) 320000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-384317048221445941) 25600000000000000000),
            (exactRationalLiteral (55212040588503651) 1600000000000000000),
            (exactRationalLiteral (10877090039173893) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (413550805438939349) 204800000000000000000),
            (exactRationalLiteral (-156741709125142149) 12800000000000000000),
            (exactRationalLiteral (-24769188397342617) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (155737094059020683) 24576000000000000000),
            (exactRationalLiteral (68357012299558183) 12800000000000000000),
            (exactRationalLiteral (293386730169443) 32000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3656449219182712163) 307200000000000000000),
            (exactRationalLiteral (62540798609745523) 6400000000000000000),
            (exactRationalLiteral (499155703569299) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5171953095907401217) 204800000000000000000),
            (exactRationalLiteral (-22364047137685659) 2560000000000000000),
            (exactRationalLiteral (2415564041580933) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8284884484735082717) 409600000000000000000),
            (exactRationalLiteral (-625674158987812803) 25600000000000000000),
            (exactRationalLiteral (-29897833362617823) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14596538865623338757) 614400000000000000000),
            (exactRationalLiteral (303594184732444961) 12800000000000000000),
            (exactRationalLiteral (7898191838099789) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2831002648949269157) 1228800000000000000000),
            (exactRationalLiteral (-10715165673636421) 5120000000000000000),
            (exactRationalLiteral (2092635907856519) 320000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (133628329934033719) 614400000000000000000),
            (exactRationalLiteral (49078467353389739) 12800000000000000000),
            (exactRationalLiteral (-214885392400601) 32000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (213467948600103971) 24576000000000000000),
            (exactRationalLiteral (-94772094270690889) 12800000000000000000),
            (exactRationalLiteral (2480253654355379) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (19104852148284999959) 614400000000000000000),
            (exactRationalLiteral (-220075997030973181) 12800000000000000000),
            (exactRationalLiteral (5603049400745183) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-7270796587526486843) 409600000000000000000),
            (exactRationalLiteral (391596641852720411) 25600000000000000000),
            (exactRationalLiteral (-13198922553489321) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7261734222367085493) 409600000000000000000),
            (exactRationalLiteral (173419011941947477) 25600000000000000000),
            (exactRationalLiteral (-2056803166860711) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-521784714104995091) 102400000000000000000),
            (exactRationalLiteral (8101752545635139) 6400000000000000000),
            (exactRationalLiteral (444487561741743) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-927116026824119167) 10240000000000000000),
            (exactRationalLiteral (135082898191335221) 3200000000000000000),
            (exactRationalLiteral (-2636969725535493) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (117085115840886733673) 614400000000000000000),
            (exactRationalLiteral (-1191968435158653363) 12800000000000000000),
            (exactRationalLiteral (22194582417608129) 800000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-927116026824119167) 10240000000000000000),
            (exactRationalLiteral (135082898191335221) 3200000000000000000),
            (exactRationalLiteral (-2636969725535493) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-521784714104995091) 102400000000000000000),
            (exactRationalLiteral (8101752545635139) 6400000000000000000),
            (exactRationalLiteral (444487561741743) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-7261734222367085493) 409600000000000000000),
            (exactRationalLiteral (173419011941947477) 25600000000000000000),
            (exactRationalLiteral (-2056803166860711) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7270796587526486843) 409600000000000000000),
            (exactRationalLiteral (391596641852720411) 25600000000000000000),
            (exactRationalLiteral (-13198922553489321) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (19104852148284999959) 614400000000000000000),
            (exactRationalLiteral (-220075997030973181) 12800000000000000000),
            (exactRationalLiteral (5603049400745183) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (213467948600103971) 24576000000000000000),
            (exactRationalLiteral (-94772094270690889) 12800000000000000000),
            (exactRationalLiteral (2480253654355379) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (133628329934033719) 614400000000000000000),
            (exactRationalLiteral (49078467353389739) 12800000000000000000),
            (exactRationalLiteral (-214885392400601) 32000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2831002648949269157) 1228800000000000000000),
            (exactRationalLiteral (-10715165673636421) 5120000000000000000),
            (exactRationalLiteral (2092635907856519) 320000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (14596538865623338757) 614400000000000000000),
            (exactRationalLiteral (303594184732444961) 12800000000000000000),
            (exactRationalLiteral (7898191838099789) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-8284884484735082717) 409600000000000000000),
            (exactRationalLiteral (-625674158987812803) 25600000000000000000),
            (exactRationalLiteral (-29897833362617823) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5171953095907401217) 204800000000000000000),
            (exactRationalLiteral (-22364047137685659) 2560000000000000000),
            (exactRationalLiteral (2415564041580933) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3656449219182712163) 307200000000000000000),
            (exactRationalLiteral (62540798609745523) 6400000000000000000),
            (exactRationalLiteral (499155703569299) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (155737094059020683) 24576000000000000000),
            (exactRationalLiteral (68357012299558183) 12800000000000000000),
            (exactRationalLiteral (293386730169443) 32000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (413550805438939349) 204800000000000000000),
            (exactRationalLiteral (-156741709125142149) 12800000000000000000),
            (exactRationalLiteral (-24769188397342617) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-384317048221445941) 25600000000000000000),
            (exactRationalLiteral (55212040588503651) 1600000000000000000),
            (exactRationalLiteral (10877090039173893) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (31424747382216299413) 409600000000000000000),
            (exactRationalLiteral (521992037119783547) 25600000000000000000),
            (exactRationalLiteral (-68266921785467589) 320000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-31265163344920650653) 409600000000000000000),
            (exactRationalLiteral (-3741499756869260483) 25600000000000000000),
            (exactRationalLiteral (329542535804094561) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1296221354292781827) 204800000000000000000),
            (exactRationalLiteral (1887063110059091683) 12800000000000000000),
            (exactRationalLiteral (-13224711915247629) 160000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1257775249994114561) 61440000000000000000),
            (exactRationalLiteral (-56879253818556191) 1280000000000000000),
            (exactRationalLiteral (-112836245366287) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 409600000000000000000),
            (exactRationalLiteral (-32695951386181797) 25600000000000000000),
            (exactRationalLiteral (10898650462060599) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (3632883487353533) 19200000000000000000),
          (exactRationalLiteral (11148695861220311) 480000000000000000),
          (exactRationalLiteral (50644103158335441) 3200000000000000000),
          (exactRationalLiteral (12996266994151870213) 153600000000000000000),
          (exactRationalLiteral (1982936387942003059) 25600000000000000000),
          (exactRationalLiteral (40221107191858331) 2400000000000000000),
          (exactRationalLiteral (8536762406191531) 3200000000000000000),
          (exactRationalLiteral (515157808434870509) 76800000000000000000),
          (exactRationalLiteral (480684470493555287) 38400000000000000000),
          (exactRationalLiteral (1980451418101406213) 76800000000000000000),
          (exactRationalLiteral (3352918715138849317) 153600000000000000000),
          (exactRationalLiteral (1941408450042490963) 76800000000000000000),
          (exactRationalLiteral (369826199305148311) 153600000000000000000),
          (exactRationalLiteral (10999817757978619) 25600000000000000000),
          (exactRationalLiteral (3517672547971589) 384000000000000000),
          (exactRationalLiteral (2472803168721313) 76800000000000000),
          (exactRationalLiteral (359816110109479627) 19200000000000000000),
          (exactRationalLiteral (348615663786700613) 19200000000000000000),
          (exactRationalLiteral (24816614077496423) 4800000000000000000),
          (exactRationalLiteral (89500386381133741) 960000000000000000),
          (exactRationalLiteral (1886388276000073447) 9600000000000000000),
          (exactRationalLiteral (89500386381133741) 960000000000000000),
          (exactRationalLiteral (24816614077496423) 4800000000000000000),
          (exactRationalLiteral (348615663786700613) 19200000000000000000),
          (exactRationalLiteral (359816110109479627) 19200000000000000000),
          (exactRationalLiteral (2472803168721313) 76800000000000000),
          (exactRationalLiteral (3517672547971589) 384000000000000000),
          (exactRationalLiteral (10999817757978619) 25600000000000000000),
          (exactRationalLiteral (369826199305148311) 153600000000000000000),
          (exactRationalLiteral (1941408450042490963) 76800000000000000000),
          (exactRationalLiteral (3352918715138849317) 153600000000000000000),
          (exactRationalLiteral (1980451418101406213) 76800000000000000000),
          (exactRationalLiteral (480684470493555287) 38400000000000000000),
          (exactRationalLiteral (515157808434870509) 76800000000000000000),
          (exactRationalLiteral (8536762406191531) 3200000000000000000),
          (exactRationalLiteral (40221107191858331) 2400000000000000000),
          (exactRationalLiteral (1982936387942003059) 25600000000000000000),
          (exactRationalLiteral (12996266994151870213) 153600000000000000000),
          (exactRationalLiteral (50644103158335441) 3200000000000000000),
          (exactRationalLiteral (11148695861220311) 480000000000000000),
          (exactRationalLiteral (3632883487353533) 19200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (39, 2),
      (38, 58),
      (38, 50),
      (38, 42),
      (38, 34),
      (38, 26),
      (38, 18),
      (38, 10),
      (38, 2),
      (37, 58),
      (37, 50),
      (37, 42),
      (37, 34),
      (37, 26),
      (37, 18),
      (37, 10),
      (37, 2),
      (36, 58),
      (36, 50),
      (36, 42),
      (36, 34),
      (36, 26),
      (36, 18),
      (36, 10),
      (36, 2),
      (35, 58),
      (35, 50),
      (35, 42),
      (35, 34),
      (35, 26),
      (35, 18),
      (35, 10),
      (35, 2),
      (34, 58),
      (34, 53),
      (34, 61),
      (35, 5),
      (35, 13),
      (35, 21),
      (35, 29),
      (35, 37),
      (35, 45),
      (35, 53),
      (35, 61),
      (36, 5),
      (36, 13),
      (36, 21),
      (36, 29),
      (36, 37),
      (36, 45),
      (36, 53),
      (36, 61),
      (37, 5)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (7) 8)
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
            (exactRationalLiteral (3632883487353533) 1228800000000000000000),
            (exactRationalLiteral (-3632883487353533) 25600000000000000000),
            (exactRationalLiteral (3632883487353533) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (923477151958257691) 61440000000000000000),
            (exactRationalLiteral (-53164868890083479) 1280000000000000000),
            (exactRationalLiteral (1970028709602643) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (2147927253163301511) 204800000000000000000),
            (exactRationalLiteral (1524343810218417931) 12800000000000000000),
            (exactRationalLiteral (-115236090344098731) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-111800172188388475957) 1228800000000000000000),
            (exactRationalLiteral (-435685326936586031) 5120000000000000000),
            (exactRationalLiteral (451994025289070603) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (92963156434078527373) 1228800000000000000000),
            (exactRationalLiteral (-1016857712670076637) 25600000000000000000),
            (exactRationalLiteral (-428090265967592147) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-682198350046113241) 76800000000000000000),
            (exactRationalLiteral (103198136053757203) 1600000000000000000),
            (exactRationalLiteral (13115957693452883) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (-5645109036868241) 204800000000000000000),
            (exactRationalLiteral (-265772076668741853) 12800000000000000000),
            (exactRationalLiteral (-5949199074891447) 160000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1465888679686737619) 204800000000000000000),
            (exactRationalLiteral (32235514459123) 4096000000000000),
            (exactRationalLiteral (8854816938364521) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (53825831118537363) 4096000000000000000),
            (exactRationalLiteral (64164148727165387) 6400000000000000000),
            (exactRationalLiteral (312519355140633) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-16154098270541833961) 614400000000000000000),
            (exactRationalLiteral (-100310148116120431) 12800000000000000000),
            (exactRationalLiteral (3339479744572999) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-28983314727317574901) 1228800000000000000000),
            (exactRationalLiteral (-753186651855302123) 25600000000000000000),
            (exactRationalLiteral (-33858413071126837) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16514895116114843567) 614400000000000000000),
            (exactRationalLiteral (67238674420932581) 2560000000000000000),
            (exactRationalLiteral (8401401848009183) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-602610291345744211) 245760000000000000000),
            (exactRationalLiteral (-4799106231926929) 25600000000000000000),
            (exactRationalLiteral (13925181528844993) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (357619905352823813) 614400000000000000000),
            (exactRationalLiteral (24583122622645619) 12800000000000000000),
            (exactRationalLiteral (-1375107511071407) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (4799266649416283921) 614400000000000000000),
            (exactRationalLiteral (-84132351560486657) 12800000000000000000),
            (exactRationalLiteral (2839617700746737) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (17847344261385311477) 614400000000000000000),
            (exactRationalLiteral (-39961609637877649) 2560000000000000000),
            (exactRationalLiteral (906185004009457) 160000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-19609560252436158691) 1228800000000000000000),
            (exactRationalLiteral (344619316473188739) 25600000000000000000),
            (exactRationalLiteral (-2057948027255303) 320000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20771191274082634637) 1228800000000000000000),
            (exactRationalLiteral (164281278959137389) 25600000000000000000),
            (exactRationalLiteral (-2512063324544333) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-302382173351085727) 61440000000000000000),
            (exactRationalLiteral (1925831513004911) 1280000000000000000),
            (exactRationalLiteral (63842989590593) 80000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-13126592130968210791) 153600000000000000000),
            (exactRationalLiteral (125182278765188901) 3200000000000000000),
            (exactRationalLiteral (-2313339987537667) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (110189682055832651371) 614400000000000000000),
            (exactRationalLiteral (-1108169187044950683) 12800000000000000000),
            (exactRationalLiteral (19705041639243211) 800000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-13126592130968210791) 153600000000000000000),
            (exactRationalLiteral (125182278765188901) 3200000000000000000),
            (exactRationalLiteral (-2313339987537667) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-302382173351085727) 61440000000000000000),
            (exactRationalLiteral (1925831513004911) 1280000000000000000),
            (exactRationalLiteral (63842989590593) 80000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-20771191274082634637) 1228800000000000000000),
            (exactRationalLiteral (164281278959137389) 25600000000000000000),
            (exactRationalLiteral (-2512063324544333) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19609560252436158691) 1228800000000000000000),
            (exactRationalLiteral (344619316473188739) 25600000000000000000),
            (exactRationalLiteral (-2057948027255303) 320000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (17847344261385311477) 614400000000000000000),
            (exactRationalLiteral (-39961609637877649) 2560000000000000000),
            (exactRationalLiteral (906185004009457) 160000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (4799266649416283921) 614400000000000000000),
            (exactRationalLiteral (-84132351560486657) 12800000000000000000),
            (exactRationalLiteral (2839617700746737) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (357619905352823813) 614400000000000000000),
            (exactRationalLiteral (24583122622645619) 12800000000000000000),
            (exactRationalLiteral (-1375107511071407) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-602610291345744211) 245760000000000000000),
            (exactRationalLiteral (-4799106231926929) 25600000000000000000),
            (exactRationalLiteral (13925181528844993) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (16514895116114843567) 614400000000000000000),
            (exactRationalLiteral (67238674420932581) 2560000000000000000),
            (exactRationalLiteral (8401401848009183) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-28983314727317574901) 1228800000000000000000),
            (exactRationalLiteral (-753186651855302123) 25600000000000000000),
            (exactRationalLiteral (-33858413071126837) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16154098270541833961) 614400000000000000000),
            (exactRationalLiteral (-100310148116120431) 12800000000000000000),
            (exactRationalLiteral (3339479744572999) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (53825831118537363) 4096000000000000000),
            (exactRationalLiteral (64164148727165387) 6400000000000000000),
            (exactRationalLiteral (312519355140633) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1465888679686737619) 204800000000000000000),
            (exactRationalLiteral (32235514459123) 4096000000000000),
            (exactRationalLiteral (8854816938364521) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5645109036868241) 204800000000000000000),
            (exactRationalLiteral (-265772076668741853) 12800000000000000000),
            (exactRationalLiteral (-5949199074891447) 160000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-682198350046113241) 76800000000000000000),
            (exactRationalLiteral (103198136053757203) 1600000000000000000),
            (exactRationalLiteral (13115957693452883) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (92963156434078527373) 1228800000000000000000),
            (exactRationalLiteral (-1016857712670076637) 25600000000000000000),
            (exactRationalLiteral (-428090265967592147) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-111800172188388475957) 1228800000000000000000),
            (exactRationalLiteral (-435685326936586031) 5120000000000000000),
            (exactRationalLiteral (451994025289070603) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2147927253163301511) 204800000000000000000),
            (exactRationalLiteral (1524343810218417931) 12800000000000000000),
            (exactRationalLiteral (-115236090344098731) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (923477151958257691) 61440000000000000000),
            (exactRationalLiteral (-53164868890083479) 1280000000000000000),
            (exactRationalLiteral (1970028709602643) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 1228800000000000000000),
            (exactRationalLiteral (-3632883487353533) 25600000000000000000),
            (exactRationalLiteral (3632883487353533) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (3632883487353533) 153600000000000000000),
          (exactRationalLiteral (45326683844992983) 2560000000000000000),
          (exactRationalLiteral (86641834747143) 5000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (11846604575338263493) 153600000000000000000),
          (exactRationalLiteral (14899442483658839) 1200000000000000000),
          (exactRationalLiteral (4608042128137) 3125000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (5924817862273973) 2400000000000000000),
          (exactRationalLiteral (40038179607619) 60000000000000000),
          (exactRationalLiteral (632500359397098553) 76800000000000000000),
          (exactRationalLiteral (2307612155400495877) 76800000000000000000),
          (exactRationalLiteral (2584467751684145107) 153600000000000000000),
          (exactRationalLiteral (2658917958856854749) 153600000000000000000),
          (exactRationalLiteral (192472257287468627) 38400000000000000000),
          (exactRationalLiteral (422163775065480919) 4800000000000000000),
          (exactRationalLiteral (4732272896344767313) 25600000000000000000),
          (exactRationalLiteral (422163775065480919) 4800000000000000000),
          (exactRationalLiteral (192472257287468627) 38400000000000000000),
          (exactRationalLiteral (2658917958856854749) 153600000000000000000),
          (exactRationalLiteral (2584467751684145107) 153600000000000000000),
          (exactRationalLiteral (2307612155400495877) 76800000000000000000),
          (exactRationalLiteral (632500359397098553) 76800000000000000000),
          (exactRationalLiteral (40038179607619) 60000000000000000),
          (exactRationalLiteral (5924817862273973) 2400000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (4608042128137) 3125000000000000),
          (exactRationalLiteral (14899442483658839) 1200000000000000000),
          (exactRationalLiteral (11846604575338263493) 153600000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (86641834747143) 5000000000000000),
          (exactRationalLiteral (45326683844992983) 2560000000000000000),
          (exactRationalLiteral (3632883487353533) 153600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (39, 3),
      (38, 59),
      (38, 51),
      (38, 43),
      (38, 35),
      (38, 27),
      (38, 19),
      (38, 11),
      (38, 3),
      (37, 59),
      (37, 51),
      (37, 43),
      (37, 35),
      (37, 27),
      (37, 19),
      (37, 11),
      (37, 3),
      (36, 59),
      (36, 51),
      (36, 43),
      (36, 35),
      (36, 27),
      (36, 19),
      (36, 11),
      (36, 3),
      (35, 59),
      (35, 51),
      (35, 43),
      (35, 35),
      (35, 27),
      (35, 19),
      (35, 11),
      (35, 3),
      (34, 59),
      (34, 52),
      (34, 60),
      (35, 4),
      (35, 12),
      (35, 20),
      (35, 28),
      (35, 36),
      (35, 44),
      (35, 52),
      (35, 60),
      (36, 4),
      (36, 12),
      (36, 20),
      (36, 28),
      (36, 36),
      (36, 44),
      (36, 52),
      (36, 60),
      (37, 4)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 7
        lower := (0 : ℚ)
        width := (exactRationalLiteral (1) 16)
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
            (exactRationalLiteral (108227231971749101603) 9830400000000000000000),
            (exactRationalLiteral (-3491201031346745213) 102400000000000000000),
            (exactRationalLiteral (112619388107959523) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3476819921567143971) 163840000000000000000),
            (exactRationalLiteral (434661907690194561) 5120000000000000000),
            (exactRationalLiteral (-26261484427844199) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-153833315769245494791) 1638400000000000000000),
            (exactRationalLiteral (-1187057467096251893) 51200000000000000000),
            (exactRationalLiteral (96331903089156207) 320000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (651218254446661804853) 9830400000000000000000),
            (exactRationalLiteral (-9654162143831484907) 102400000000000000000),
            (exactRationalLiteral (-871558546954011403) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4629886813275218813) 9830400000000000000000),
            (exactRationalLiteral (9110286216133490563) 102400000000000000000),
            (exactRationalLiteral (80355299029700327) 640000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2489287236018308509) 614400000000000000000),
            (exactRationalLiteral (-167214699601190321) 6400000000000000000),
            (exactRationalLiteral (-6231665600139589) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (981526695583442817) 1638400000000000000000),
            (exactRationalLiteral (294699822885374979) 51200000000000000000),
            (exactRationalLiteral (12671710419247491) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1050766379222739143) 196608000000000000000),
            (exactRationalLiteral (15007687564764607) 51200000000000000000),
            (exactRationalLiteral (-173300881725337) 64000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (13819284531021864779) 2457600000000000000000),
            (exactRationalLiteral (141923765198094067) 25600000000000000000),
            (exactRationalLiteral (3331265762496923) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-88740529868946157583) 4915200000000000000000),
            (exactRationalLiteral (-80022737945357171) 10240000000000000000),
            (exactRationalLiteral (-6717818204238959) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-92309826074388308683) 9830400000000000000000),
            (exactRationalLiteral (-750594458598535787) 102400000000000000000),
            (exactRationalLiteral (-10288420368872971) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (51380946695710289881) 4915200000000000000000),
            (exactRationalLiteral (581810683216486569) 51200000000000000000),
            (exactRationalLiteral (9506258552332153) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (5614760047713975119) 9830400000000000000000),
            (exactRationalLiteral (-35749129132547709) 20480000000000000000),
            (exactRationalLiteral (-4469733158192957) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-7351561718705514191) 1638400000000000000000),
            (exactRationalLiteral (263713992495683331) 51200000000000000000),
            (exactRationalLiteral (321930587869803) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (3104745503705129911) 196608000000000000000),
            (exactRationalLiteral (-514812478021002081) 51200000000000000000),
            (exactRationalLiteral (468456728818783) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (248249023272568718347) 4915200000000000000000),
            (exactRationalLiteral (-1775647797166504149) 51200000000000000000),
            (exactRationalLiteral (24607653560214091) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-364202057866511808157) 9830400000000000000000),
            (exactRationalLiteral (3795398328138815619) 102400000000000000000),
            (exactRationalLiteral (-62762625322138717) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-230463616813218664307) 9830400000000000000000),
            (exactRationalLiteral (757087565177729133) 102400000000000000000),
            (exactRationalLiteral (1577145637323853) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12307838250454059509) 2457600000000000000000),
            (exactRationalLiteral (-51189437800626869) 25600000000000000000),
            (exactRationalLiteral (2454882795843211) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-32839157295032196143) 245760000000000000000),
            (exactRationalLiteral (905162858443210809) 12800000000000000000),
            (exactRationalLiteral (-9319311176043811) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (465650226223898761303) 1638400000000000000000),
            (exactRationalLiteral (-7765313475634463227) 51200000000000000000),
            (exactRationalLiteral (75508424564777733) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-32839157295032196143) 245760000000000000000),
            (exactRationalLiteral (905162858443210809) 12800000000000000000),
            (exactRationalLiteral (-9319311176043811) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12307838250454059509) 2457600000000000000000),
            (exactRationalLiteral (-51189437800626869) 25600000000000000000),
            (exactRationalLiteral (2454882795843211) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-230463616813218664307) 9830400000000000000000),
            (exactRationalLiteral (757087565177729133) 102400000000000000000),
            (exactRationalLiteral (1577145637323853) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-364202057866511808157) 9830400000000000000000),
            (exactRationalLiteral (3795398328138815619) 102400000000000000000),
            (exactRationalLiteral (-62762625322138717) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (248249023272568718347) 4915200000000000000000),
            (exactRationalLiteral (-1775647797166504149) 51200000000000000000),
            (exactRationalLiteral (24607653560214091) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3104745503705129911) 196608000000000000000),
            (exactRationalLiteral (-514812478021002081) 51200000000000000000),
            (exactRationalLiteral (468456728818783) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-7351561718705514191) 1638400000000000000000),
            (exactRationalLiteral (263713992495683331) 51200000000000000000),
            (exactRationalLiteral (321930587869803) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (5614760047713975119) 9830400000000000000000),
            (exactRationalLiteral (-35749129132547709) 20480000000000000000),
            (exactRationalLiteral (-4469733158192957) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (51380946695710289881) 4915200000000000000000),
            (exactRationalLiteral (581810683216486569) 51200000000000000000),
            (exactRationalLiteral (9506258552332153) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-92309826074388308683) 9830400000000000000000),
            (exactRationalLiteral (-750594458598535787) 102400000000000000000),
            (exactRationalLiteral (-10288420368872971) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-88740529868946157583) 4915200000000000000000),
            (exactRationalLiteral (-80022737945357171) 10240000000000000000),
            (exactRationalLiteral (-6717818204238959) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (13819284531021864779) 2457600000000000000000),
            (exactRationalLiteral (141923765198094067) 25600000000000000000),
            (exactRationalLiteral (3331265762496923) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1050766379222739143) 196608000000000000000),
            (exactRationalLiteral (15007687564764607) 51200000000000000000),
            (exactRationalLiteral (-173300881725337) 64000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (981526695583442817) 1638400000000000000000),
            (exactRationalLiteral (294699822885374979) 51200000000000000000),
            (exactRationalLiteral (12671710419247491) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2489287236018308509) 614400000000000000000),
            (exactRationalLiteral (-167214699601190321) 6400000000000000000),
            (exactRationalLiteral (-6231665600139589) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (-4629886813275218813) 9830400000000000000000),
            (exactRationalLiteral (9110286216133490563) 102400000000000000000),
            (exactRationalLiteral (80355299029700327) 640000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (651218254446661804853) 9830400000000000000000),
            (exactRationalLiteral (-9654162143831484907) 102400000000000000000),
            (exactRationalLiteral (-871558546954011403) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-153833315769245494791) 1638400000000000000000),
            (exactRationalLiteral (-1187057467096251893) 51200000000000000000),
            (exactRationalLiteral (96331903089156207) 320000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3476819921567143971) 163840000000000000000),
            (exactRationalLiteral (434661907690194561) 5120000000000000000),
            (exactRationalLiteral (-26261484427844199) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (108227231971749101603) 9830400000000000000000),
            (exactRationalLiteral (-3491201031346745213) 102400000000000000000),
            (exactRationalLiteral (112619388107959523) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (3632883487353533) 300000000000000000),
          (exactRationalLiteral (1457087808370745933) 61440000000000000000),
          (exactRationalLiteral (3863672478567265227) 40960000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (468628511775361) 150000000000000000),
          (exactRationalLiteral (125354454074798281) 25600000000000000000),
          (exactRationalLiteral (161008595132318273) 204800000000000000000),
          (exactRationalLiteral (3287743131434429543) 614400000000000000000),
          (exactRationalLiteral (1781869538216177927) 307200000000000000000),
          (exactRationalLiteral (3748356768120322333) 204800000000000000000),
          (exactRationalLiteral (3941435625047699561) 409600000000000000000),
          (exactRationalLiteral (6644393640752712593) 614400000000000000000),
          (exactRationalLiteral (58004569877) 93750000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (518921022990637703) 102400000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (21674719072611743) 75000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (518921022990637703) 102400000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (58004569877) 93750000000000),
          (exactRationalLiteral (6644393640752712593) 614400000000000000000),
          (exactRationalLiteral (3941435625047699561) 409600000000000000000),
          (exactRationalLiteral (3748356768120322333) 204800000000000000000),
          (exactRationalLiteral (1781869538216177927) 307200000000000000000),
          (exactRationalLiteral (3287743131434429543) 614400000000000000000),
          (exactRationalLiteral (161008595132318273) 204800000000000000000),
          (exactRationalLiteral (125354454074798281) 25600000000000000000),
          (exactRationalLiteral (468628511775361) 150000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (3863672478567265227) 40960000000000000000),
          (exactRationalLiteral (1457087808370745933) 61440000000000000000),
          (exactRationalLiteral (3632883487353533) 300000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 32),
      (31, 16),
      (31, 0),
      (30, 48),
      (30, 32),
      (30, 16),
      (30, 0),
      (29, 48),
      (29, 32),
      (29, 16),
      (29, 0),
      (28, 48),
      (28, 32),
      (28, 16),
      (28, 0),
      (27, 48),
      (27, 32),
      (27, 16),
      (27, 0),
      (26, 48),
      (26, 32),
      (26, 16),
      (26, 0),
      (25, 48),
      (25, 32),
      (25, 16),
      (25, 0),
      (24, 48),
      (24, 32),
      (24, 16),
      (24, 0),
      (23, 48),
      (23, 32),
      (23, 16),
      (23, 31),
      (23, 47),
      (23, 63),
      (24, 15),
      (24, 31),
      (24, 47),
      (24, 63),
      (25, 15),
      (25, 31),
      (25, 47),
      (25, 63),
      (26, 15),
      (26, 31),
      (26, 47),
      (26, 63),
      (27, 15),
      (27, 31),
      (27, 47),
      (27, 63)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (1) 16)
        width := (exactRationalLiteral (1) 16)
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
            (exactRationalLiteral (88602395373065316337) 9830400000000000000000),
            (exactRationalLiteral (-3055255012864321253) 102400000000000000000),
            (exactRationalLiteral (105353621133252457) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12731624857528344611) 491520000000000000000),
            (exactRationalLiteral (534050719822009) 8192000000000000),
            (exactRationalLiteral (-24178619472875269) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-30869255203202404377) 327680000000000000000),
            (exactRationalLiteral (25654221326046043) 2048000000000000000),
            (exactRationalLiteral (432546984677920449) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (583324384978164662743) 9830400000000000000000),
            (exactRationalLiteral (-2579098670535515687) 20480000000000000000),
            (exactRationalLiteral (-749107057469035361) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (54506125797146727377) 9830400000000000000000),
            (exactRationalLiteral (10543880882646988699) 102400000000000000000),
            (exactRationalLiteral (315020838108247433) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3558399950210009543) 614400000000000000000),
            (exactRationalLiteral (-187663626693190697) 6400000000000000000),
            (exactRationalLiteral (-3992797945860599) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (322995488079005983) 327680000000000000000),
            (exactRationalLiteral (335433050608135707) 51200000000000000000),
            (exactRationalLiteral (7694903442132873) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8771098645391992967) 1638400000000000000000),
            (exactRationalLiteral (717896760487799) 51200000000000000000),
            (exactRationalLiteral (-2812373359004979) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4903351921988892531) 819200000000000000000),
            (exactRationalLiteral (154875555551224427) 25600000000000000000),
            (exactRationalLiteral (3144629414068257) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-91218130162945771957) 4915200000000000000000),
            (exactRationalLiteral (-425137131137757559) 51200000000000000000),
            (exactRationalLiteral (-5793902501246893) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-96952696189240035113) 9830400000000000000000),
            (exactRationalLiteral (-799669299491045699) 102400000000000000000),
            (exactRationalLiteral (-2849800015476397) 640000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (54987898737676832707) 4915200000000000000000),
            (exactRationalLiteral (620842137445633969) 51200000000000000000),
            (exactRationalLiteral (10009468562241547) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (4287950192204216021) 9830400000000000000000),
            (exactRationalLiteral (-261216304847472889) 102400000000000000000),
            (exactRationalLiteral (-18886663801402387) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-20381835635762869727) 4915200000000000000000),
            (exactRationalLiteral (292900245791979611) 51200000000000000000),
            (exactRationalLiteral (1308972390280613) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (74536821661433626117) 4915200000000000000000),
            (exactRationalLiteral (-512219923012944233) 51200000000000000000),
            (exactRationalLiteral (827820775210141) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (237886139834769470953) 4915200000000000000000),
            (exactRationalLiteral (-1679361431687043581) 51200000000000000000),
            (exactRationalLiteral (23535529179516193) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-342171182671875727823) 9830400000000000000000),
            (exactRationalLiteral (3550166191684686363) 102400000000000000000),
            (exactRationalLiteral (-59853442904925911) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-225903986715135137761) 9830400000000000000000),
            (exactRationalLiteral (762485627411657301) 102400000000000000000),
            (exactRationalLiteral (1121885479640231) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12586017374162857303) 2457600000000000000000),
            (exactRationalLiteral (-41620451844831581) 25600000000000000000),
            (exactRationalLiteral (2329610182054433) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-158875346539662250289) 1228800000000000000000),
            (exactRationalLiteral (868532873215031217) 12800000000000000000),
            (exactRationalLiteral (-1799136287609197) 80000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1351254940749553377671) 4915200000000000000000),
            (exactRationalLiteral (-7468258858932082131) 51200000000000000000),
            (exactRationalLiteral (14603776757282563) 320000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-158875346539662250289) 1228800000000000000000),
            (exactRationalLiteral (868532873215031217) 12800000000000000000),
            (exactRationalLiteral (-1799136287609197) 80000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12586017374162857303) 2457600000000000000000),
            (exactRationalLiteral (-41620451844831581) 25600000000000000000),
            (exactRationalLiteral (2329610182054433) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-225903986715135137761) 9830400000000000000000),
            (exactRationalLiteral (762485627411657301) 102400000000000000000),
            (exactRationalLiteral (1121885479640231) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-342171182671875727823) 9830400000000000000000),
            (exactRationalLiteral (3550166191684686363) 102400000000000000000),
            (exactRationalLiteral (-59853442904925911) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (237886139834769470953) 4915200000000000000000),
            (exactRationalLiteral (-1679361431687043581) 51200000000000000000),
            (exactRationalLiteral (23535529179516193) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (74536821661433626117) 4915200000000000000000),
            (exactRationalLiteral (-512219923012944233) 51200000000000000000),
            (exactRationalLiteral (827820775210141) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-20381835635762869727) 4915200000000000000000),
            (exactRationalLiteral (292900245791979611) 51200000000000000000),
            (exactRationalLiteral (1308972390280613) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (4287950192204216021) 9830400000000000000000),
            (exactRationalLiteral (-261216304847472889) 102400000000000000000),
            (exactRationalLiteral (-18886663801402387) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (54987898737676832707) 4915200000000000000000),
            (exactRationalLiteral (620842137445633969) 51200000000000000000),
            (exactRationalLiteral (10009468562241547) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-96952696189240035113) 9830400000000000000000),
            (exactRationalLiteral (-799669299491045699) 102400000000000000000),
            (exactRationalLiteral (-2849800015476397) 640000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-91218130162945771957) 4915200000000000000000),
            (exactRationalLiteral (-425137131137757559) 51200000000000000000),
            (exactRationalLiteral (-5793902501246893) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4903351921988892531) 819200000000000000000),
            (exactRationalLiteral (154875555551224427) 25600000000000000000),
            (exactRationalLiteral (3144629414068257) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (8771098645391992967) 1638400000000000000000),
            (exactRationalLiteral (717896760487799) 51200000000000000000),
            (exactRationalLiteral (-2812373359004979) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (322995488079005983) 327680000000000000000),
            (exactRationalLiteral (335433050608135707) 51200000000000000000),
            (exactRationalLiteral (7694903442132873) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3558399950210009543) 614400000000000000000),
            (exactRationalLiteral (-187663626693190697) 6400000000000000000),
            (exactRationalLiteral (-3992797945860599) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (54506125797146727377) 9830400000000000000000),
            (exactRationalLiteral (10543880882646988699) 102400000000000000000),
            (exactRationalLiteral (315020838108247433) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (583324384978164662743) 9830400000000000000000),
            (exactRationalLiteral (-2579098670535515687) 20480000000000000000),
            (exactRationalLiteral (-749107057469035361) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-30869255203202404377) 327680000000000000000),
            (exactRationalLiteral (25654221326046043) 2048000000000000000),
            (exactRationalLiteral (432546984677920449) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (12731624857528344611) 491520000000000000000),
            (exactRationalLiteral (534050719822009) 8192000000000000),
            (exactRationalLiteral (-24178619472875269) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (88602395373065316337) 9830400000000000000000),
            (exactRationalLiteral (-3055255012864321253) 102400000000000000000),
            (exactRationalLiteral (105353621133252457) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
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
        bound := ![
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (exactRationalLiteral (32695951386181797) 3276800000000000000),
          (exactRationalLiteral (71153518391945157) 2560000000000000000),
          (exactRationalLiteral (29008580426953066717) 307200000000000000000),
          (exactRationalLiteral (25820929921626991831) 409600000000000000000),
          (exactRationalLiteral (1359991455170192323) 153600000000000000000),
          (exactRationalLiteral (32283201486718937) 4800000000000000000),
          (exactRationalLiteral (30582436353371553) 25600000000000000000),
          (exactRationalLiteral (548253135148261673) 102400000000000000000),
          (exactRationalLiteral (237250359417005333) 38400000000000000000),
          (exactRationalLiteral (289095191581285279) 15360000000000000000),
          (exactRationalLiteral (1553069240278118323) 153600000000000000000),
          (exactRationalLiteral (888761018136022093) 76800000000000000000),
          (exactRationalLiteral (626651014293455791) 1228800000000000000000),
          (exactRationalLiteral (531003752147798209) 122880000000000000000),
          (exactRationalLiteral (1901894630269372339) 122880000000000000000),
          (exactRationalLiteral (30374420847444937403) 614400000000000000000),
          (exactRationalLiteral (14708445673618882127) 409600000000000000000),
          (exactRationalLiteral (1901565419257102893) 81920000000000000000),
          (exactRationalLiteral (198499258366532549) 38400000000000000000),
          (exactRationalLiteral (6729503917437103367) 51200000000000000000),
          (exactRationalLiteral (171735002343512255621) 614400000000000000000),
          (exactRationalLiteral (6729503917437103367) 51200000000000000000),
          (exactRationalLiteral (198499258366532549) 38400000000000000000),
          (exactRationalLiteral (1901565419257102893) 81920000000000000000),
          (exactRationalLiteral (14708445673618882127) 409600000000000000000),
          (exactRationalLiteral (30374420847444937403) 614400000000000000000),
          (exactRationalLiteral (1901894630269372339) 122880000000000000000),
          (exactRationalLiteral (531003752147798209) 122880000000000000000),
          (exactRationalLiteral (626651014293455791) 1228800000000000000000),
          (exactRationalLiteral (888761018136022093) 76800000000000000000),
          (exactRationalLiteral (1553069240278118323) 153600000000000000000),
          (exactRationalLiteral (289095191581285279) 15360000000000000000),
          (exactRationalLiteral (237250359417005333) 38400000000000000000),
          (exactRationalLiteral (548253135148261673) 102400000000000000000),
          (exactRationalLiteral (30582436353371553) 25600000000000000000),
          (exactRationalLiteral (32283201486718937) 4800000000000000000),
          (exactRationalLiteral (1359991455170192323) 153600000000000000000),
          (exactRationalLiteral (25820929921626991831) 409600000000000000000),
          (exactRationalLiteral (29008580426953066717) 307200000000000000000),
          (exactRationalLiteral (71153518391945157) 2560000000000000000),
          (exactRationalLiteral (32695951386181797) 3276800000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 33),
      (31, 17),
      (31, 1),
      (30, 49),
      (30, 33),
      (30, 17),
      (30, 1),
      (29, 49),
      (29, 33),
      (29, 17),
      (29, 1),
      (28, 49),
      (28, 33),
      (28, 17),
      (28, 1),
      (27, 49),
      (27, 33),
      (27, 17),
      (27, 1),
      (26, 49),
      (26, 33),
      (26, 17),
      (26, 1),
      (25, 49),
      (25, 33),
      (25, 17),
      (25, 1),
      (24, 49),
      (24, 33),
      (24, 17),
      (24, 1),
      (23, 49),
      (23, 33),
      (23, 17),
      (23, 30),
      (23, 46),
      (23, 62),
      (24, 14),
      (24, 30),
      (24, 46),
      (24, 62),
      (25, 14),
      (25, 30),
      (25, 46),
      (25, 62),
      (26, 14),
      (26, 30),
      (26, 46),
      (26, 62),
      (27, 14),
      (27, 30),
      (27, 46),
      (27, 62)
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
      true
    ]
  }
]

/-- All centered cubic, true Bernstein, center and radius checks are exact. -/
theorem generatorCoordinates30_valid : ∀ i, (generatorCoordinates30 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
