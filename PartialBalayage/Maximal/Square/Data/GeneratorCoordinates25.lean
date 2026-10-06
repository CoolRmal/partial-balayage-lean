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

/-- Actual coordinate interval candidates, block 25. -/
def generatorCoordinates25 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 6
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
            (exactRationalLiteral (1688946349157141) 1200000000000000000),
            (exactRationalLiteral (-1688946349157141) 200000000000000000),
            (exactRationalLiteral (1688946349157141) 100000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2335099032284573) 75000000000000000),
            (exactRationalLiteral (-4665633130371371) 200000000000000000),
            (exactRationalLiteral (-1558254332922307) 25000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-125309504071407397) 2400000000000000000),
            (exactRationalLiteral (59068583853428567) 400000000000000000),
            (exactRationalLiteral (13202742670682843) 200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2097705196854731) 120000000000000000),
            (exactRationalLiteral (-10458871271438889) 50000000000000000),
            (exactRationalLiteral (850583838488861) 50000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (125237661915770183) 2400000000000000000),
            (exactRationalLiteral (43196488129161227) 400000000000000000),
            (exactRationalLiteral (-15560826558993193) 200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-59837724884171) 3750000000000000),
            (exactRationalLiteral (-371076942173819) 25000000000000000),
            (exactRationalLiteral (259845446656471) 5000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (113704063199393) 80000000000000000),
            (exactRationalLiteral (300069687038307) 200000000000000000),
            (exactRationalLiteral (-1425517928829129) 100000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-778038910801469) 2400000000000000000),
            (exactRationalLiteral (-470888159817571) 400000000000000000),
            (exactRationalLiteral (660780160078867) 200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10796676761390167) 2400000000000000000),
            (exactRationalLiteral (983022609221679) 400000000000000000),
            (exactRationalLiteral (-155566764250913) 200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (883838587511249) 240000000000000000),
            (exactRationalLiteral (44160810869523) 20000000000000000),
            (exactRationalLiteral (186318239050909) 100000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-35931213387332527) 2400000000000000000),
            (exactRationalLiteral (-1685931059718347) 400000000000000000),
            (exactRationalLiteral (-433910179149247) 200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-499001097910279) 80000000000000000),
            (exactRationalLiteral (-456092597869317) 100000000000000000),
            (exactRationalLiteral (-51573827837097) 20000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (292034484598407) 50000000000000000),
            (exactRationalLiteral (1295708612095419) 200000000000000000),
            (exactRationalLiteral (406610887023) 125000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-100360626669161) 300000000000000000),
            (exactRationalLiteral (454137959144989) 100000000000000000),
            (exactRationalLiteral (-103554645839141) 25000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-630153657354829) 96000000000000000),
            (exactRationalLiteral (1853527127369319) 400000000000000000),
            (exactRationalLiteral (-1024884122534437) 200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (26924809667555581) 1200000000000000000),
            (exactRationalLiteral (-3551651039120953) 200000000000000000),
            (exactRationalLiteral (1519658442459181) 100000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1864236348964397) 25000000000000000),
            (exactRationalLiteral (-1172458248311421) 20000000000000000),
            (exactRationalLiteral (151131737732607) 5000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-39264317405126599) 600000000000000000),
            (exactRationalLiteral (15328719748032933) 200000000000000000),
            (exactRationalLiteral (-566103686818211) 10000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-20788367105117627) 800000000000000000),
            (exactRationalLiteral (-229253777615453) 400000000000000000),
            (exactRationalLiteral (612123593308707) 40000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1768687376782573) 600000000000000000),
            (exactRationalLiteral (-600741063569547) 100000000000000000),
            (exactRationalLiteral (224013933323417) 50000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-17874218183224013) 100000000000000000),
            (exactRationalLiteral (20219730964629371) 200000000000000000),
            (exactRationalLiteral (-853130739653511) 25000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (456055248181311659) 1200000000000000000),
            (exactRationalLiteral (-68170580646427) 320000000000000),
            (exactRationalLiteral (6881510503952171) 100000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-17874218183224013) 100000000000000000),
            (exactRationalLiteral (20219730964629371) 200000000000000000),
            (exactRationalLiteral (-853130739653511) 25000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1768687376782573) 600000000000000000),
            (exactRationalLiteral (-600741063569547) 100000000000000000),
            (exactRationalLiteral (224013933323417) 50000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-20788367105117627) 800000000000000000),
            (exactRationalLiteral (-229253777615453) 400000000000000000),
            (exactRationalLiteral (612123593308707) 40000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-39264317405126599) 600000000000000000),
            (exactRationalLiteral (15328719748032933) 200000000000000000),
            (exactRationalLiteral (-566103686818211) 10000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (1864236348964397) 25000000000000000),
            (exactRationalLiteral (-1172458248311421) 20000000000000000),
            (exactRationalLiteral (151131737732607) 5000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (26924809667555581) 1200000000000000000),
            (exactRationalLiteral (-3551651039120953) 200000000000000000),
            (exactRationalLiteral (1519658442459181) 100000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-630153657354829) 96000000000000000),
            (exactRationalLiteral (1853527127369319) 400000000000000000),
            (exactRationalLiteral (-1024884122534437) 200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-100360626669161) 300000000000000000),
            (exactRationalLiteral (454137959144989) 100000000000000000),
            (exactRationalLiteral (-103554645839141) 25000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (292034484598407) 50000000000000000),
            (exactRationalLiteral (1295708612095419) 200000000000000000),
            (exactRationalLiteral (406610887023) 125000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-499001097910279) 80000000000000000),
            (exactRationalLiteral (-456092597869317) 100000000000000000),
            (exactRationalLiteral (-51573827837097) 20000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-35931213387332527) 2400000000000000000),
            (exactRationalLiteral (-1685931059718347) 400000000000000000),
            (exactRationalLiteral (-433910179149247) 200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (883838587511249) 240000000000000000),
            (exactRationalLiteral (44160810869523) 20000000000000000),
            (exactRationalLiteral (186318239050909) 100000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (10796676761390167) 2400000000000000000),
            (exactRationalLiteral (983022609221679) 400000000000000000),
            (exactRationalLiteral (-155566764250913) 200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-778038910801469) 2400000000000000000),
            (exactRationalLiteral (-470888159817571) 400000000000000000),
            (exactRationalLiteral (660780160078867) 200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (113704063199393) 80000000000000000),
            (exactRationalLiteral (300069687038307) 200000000000000000),
            (exactRationalLiteral (-1425517928829129) 100000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-59837724884171) 3750000000000000),
            (exactRationalLiteral (-371076942173819) 25000000000000000),
            (exactRationalLiteral (259845446656471) 5000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (125237661915770183) 2400000000000000000),
            (exactRationalLiteral (43196488129161227) 400000000000000000),
            (exactRationalLiteral (-15560826558993193) 200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2097705196854731) 120000000000000000),
            (exactRationalLiteral (-10458871271438889) 50000000000000000),
            (exactRationalLiteral (850583838488861) 50000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-125309504071407397) 2400000000000000000),
            (exactRationalLiteral (59068583853428567) 400000000000000000),
            (exactRationalLiteral (13202742670682843) 200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2335099032284573) 75000000000000000),
            (exactRationalLiteral (-4665633130371371) 200000000000000000),
            (exactRationalLiteral (-1558254332922307) 25000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 1200000000000000000),
            (exactRationalLiteral (-1688946349157141) 200000000000000000),
            (exactRationalLiteral (1688946349157141) 100000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (exactRationalLiteral (3632883487353533) 75000000000000000),
          (exactRationalLiteral (1020467580824427) 10000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (295225479525993) 3125000000000000),
          (exactRationalLiteral (37528916786427) 1250000000000000),
          (exactRationalLiteral (710147543583593) 150000000000000000),
          (exactRationalLiteral (13099755454561) 10000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (4259017811785259) 150000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (75825506778068557) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (4259017811785259) 150000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (13099755454561) 10000000000000000),
          (exactRationalLiteral (710147543583593) 150000000000000000),
          (exactRationalLiteral (37528916786427) 1250000000000000),
          (exactRationalLiteral (295225479525993) 3125000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (1020467580824427) 10000000000000000),
          (exactRationalLiteral (3632883487353533) 75000000000000000),
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (46, 28),
      (46, 27),
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
      (46, 15)
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
        cell := 6
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
            (exactRationalLiteral (15200517142414269) 3200000000000000000),
            (exactRationalLiteral (-15200517142414269) 800000000000000000),
            (exactRationalLiteral (5066839047471423) 200000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (307616268887703667) 9600000000000000000),
            (exactRationalLiteral (16135437624314189) 800000000000000000),
            (exactRationalLiteral (-22331935482421217) 200000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1584751193985961249) 19200000000000000000),
            (exactRationalLiteral (136131975928639223) 1600000000000000000),
            (exactRationalLiteral (73736874143709359) 400000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13103295529903137) 400000000000000000),
            (exactRationalLiteral (-36052323106513469) 200000000000000000),
            (exactRationalLiteral (-1658436454432737) 12500000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (432916670094305603) 19200000000000000000),
            (exactRationalLiteral (192291067080579659) 1600000000000000000),
            (exactRationalLiteral (2323307710810327) 80000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23773474834382461) 2400000000000000000),
            (exactRationalLiteral (-1197396710028233) 40000000000000000),
            (exactRationalLiteral (419913546185903) 50000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (748115110260623) 1920000000000000000),
            (exactRationalLiteral (4652318678659331) 800000000000000000),
            (exactRationalLiteral (-120200814569569) 40000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (718931171158523) 6400000000000000000),
            (exactRationalLiteral (-3292439201189019) 1600000000000000000),
            (exactRationalLiteral (87326241761001) 400000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (24708249992951501) 6400000000000000000),
            (exactRationalLiteral (162933988399663) 64000000000000000),
            (exactRationalLiteral (169874255396967) 400000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (161095837902993) 50000000000000000),
            (exactRationalLiteral (631457115807641) 400000000000000000),
            (exactRationalLiteral (6544086253191) 10000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-269358433629117907) 19200000000000000000),
            (exactRationalLiteral (-5471645350094027) 1600000000000000000),
            (exactRationalLiteral (-404258530480867) 400000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1261984107402161) 240000000000000000),
            (exactRationalLiteral (-1309512082804469) 400000000000000000),
            (exactRationalLiteral (-128494584743657) 50000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1688828912734673) 384000000000000000),
            (exactRationalLiteral (4134806747000767) 800000000000000000),
            (exactRationalLiteral (397450282144109) 200000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8128945784667137) 4800000000000000000),
            (exactRationalLiteral (495170700288817) 80000000000000000),
            (exactRationalLiteral (-49016616301513) 20000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-156547241615815697) 19200000000000000000),
            (exactRationalLiteral (13638524880826471) 1600000000000000000),
            (exactRationalLiteral (-4174648126280321) 400000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (268637850488008907) 9600000000000000000),
            (exactRationalLiteral (-21786847949678273) 800000000000000000),
            (exactRationalLiteral (4540926908276099) 200000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (438074354423926879) 4800000000000000000),
            (exactRationalLiteral (-1208800429426147) 16000000000000000),
            (exactRationalLiteral (749642202954623) 20000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-169958837103821953) 1920000000000000000),
            (exactRationalLiteral (87613275316456497) 800000000000000000),
            (exactRationalLiteral (-2995264517592109) 40000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-474858237907893221) 19200000000000000000),
            (exactRationalLiteral (-16107306460919133) 1600000000000000000),
            (exactRationalLiteral (9069055417370251) 400000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5529853662083201) 4800000000000000000),
            (exactRationalLiteral (-3365688976974173) 400000000000000000),
            (exactRationalLiteral (514696856049151) 100000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1980079096364095327) 9600000000000000000),
            (exactRationalLiteral (95571257140327023) 800000000000000000),
            (exactRationalLiteral (-7867287364581451) 200000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4203094839141738457) 9600000000000000000),
            (exactRationalLiteral (-200036929451205843) 800000000000000000),
            (exactRationalLiteral (15847456827234001) 200000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1980079096364095327) 9600000000000000000),
            (exactRationalLiteral (95571257140327023) 800000000000000000),
            (exactRationalLiteral (-7867287364581451) 200000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5529853662083201) 4800000000000000000),
            (exactRationalLiteral (-3365688976974173) 400000000000000000),
            (exactRationalLiteral (514696856049151) 100000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-474858237907893221) 19200000000000000000),
            (exactRationalLiteral (-16107306460919133) 1600000000000000000),
            (exactRationalLiteral (9069055417370251) 400000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-169958837103821953) 1920000000000000000),
            (exactRationalLiteral (87613275316456497) 800000000000000000),
            (exactRationalLiteral (-2995264517592109) 40000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (438074354423926879) 4800000000000000000),
            (exactRationalLiteral (-1208800429426147) 16000000000000000),
            (exactRationalLiteral (749642202954623) 20000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (268637850488008907) 9600000000000000000),
            (exactRationalLiteral (-21786847949678273) 800000000000000000),
            (exactRationalLiteral (4540926908276099) 200000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-156547241615815697) 19200000000000000000),
            (exactRationalLiteral (13638524880826471) 1600000000000000000),
            (exactRationalLiteral (-4174648126280321) 400000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-8128945784667137) 4800000000000000000),
            (exactRationalLiteral (495170700288817) 80000000000000000),
            (exactRationalLiteral (-49016616301513) 20000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1688828912734673) 384000000000000000),
            (exactRationalLiteral (4134806747000767) 800000000000000000),
            (exactRationalLiteral (397450282144109) 200000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1261984107402161) 240000000000000000),
            (exactRationalLiteral (-1309512082804469) 400000000000000000),
            (exactRationalLiteral (-128494584743657) 50000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-269358433629117907) 19200000000000000000),
            (exactRationalLiteral (-5471645350094027) 1600000000000000000),
            (exactRationalLiteral (-404258530480867) 400000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (161095837902993) 50000000000000000),
            (exactRationalLiteral (631457115807641) 400000000000000000),
            (exactRationalLiteral (6544086253191) 10000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (24708249992951501) 6400000000000000000),
            (exactRationalLiteral (162933988399663) 64000000000000000),
            (exactRationalLiteral (169874255396967) 400000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (718931171158523) 6400000000000000000),
            (exactRationalLiteral (-3292439201189019) 1600000000000000000),
            (exactRationalLiteral (87326241761001) 400000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (748115110260623) 1920000000000000000),
            (exactRationalLiteral (4652318678659331) 800000000000000000),
            (exactRationalLiteral (-120200814569569) 40000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-23773474834382461) 2400000000000000000),
            (exactRationalLiteral (-1197396710028233) 40000000000000000),
            (exactRationalLiteral (419913546185903) 50000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (432916670094305603) 19200000000000000000),
            (exactRationalLiteral (192291067080579659) 1600000000000000000),
            (exactRationalLiteral (2323307710810327) 80000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13103295529903137) 400000000000000000),
            (exactRationalLiteral (-36052323106513469) 200000000000000000),
            (exactRationalLiteral (-1658436454432737) 12500000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1584751193985961249) 19200000000000000000),
            (exactRationalLiteral (136131975928639223) 1600000000000000000),
            (exactRationalLiteral (73736874143709359) 400000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (307616268887703667) 9600000000000000000),
            (exactRationalLiteral (16135437624314189) 800000000000000000),
            (exactRationalLiteral (-22331935482421217) 200000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15200517142414269) 3200000000000000000),
            (exactRationalLiteral (-15200517142414269) 800000000000000000),
            (exactRationalLiteral (5066839047471423) 200000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (exactRationalLiteral (42027217646924539) 1200000000000000000),
          (exactRationalLiteral (9593497046149237) 100000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (125237661915770183) 2400000000000000000),
          (exactRationalLiteral (59837724884171) 3750000000000000),
          (exactRationalLiteral (113704063199393) 80000000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (10796676761390167) 2400000000000000000),
          (exactRationalLiteral (883838587511249) 240000000000000000),
          (exactRationalLiteral (35931213387332527) 2400000000000000000),
          (exactRationalLiteral (499001097910279) 80000000000000000),
          (exactRationalLiteral (292034484598407) 50000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (75825506778068557) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (292034484598407) 50000000000000000),
          (exactRationalLiteral (499001097910279) 80000000000000000),
          (exactRationalLiteral (35931213387332527) 2400000000000000000),
          (exactRationalLiteral (883838587511249) 240000000000000000),
          (exactRationalLiteral (10796676761390167) 2400000000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (113704063199393) 80000000000000000),
          (exactRationalLiteral (59837724884171) 3750000000000000),
          (exactRationalLiteral (125237661915770183) 2400000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (9593497046149237) 100000000000000000),
          (exactRationalLiteral (42027217646924539) 1200000000000000000),
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (45, 16),
      (45, 14),
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
      (44, 55)
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
        cell := 6
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
            (exactRationalLiteral (1688946349157141) 9600000000000000000),
            (exactRationalLiteral (-1688946349157141) 800000000000000000),
            (exactRationalLiteral (1688946349157141) 200000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (43074575079375257) 1920000000000000000),
            (exactRationalLiteral (-6745740205839927) 160000000000000000),
            (exactRationalLiteral (-520026768867139) 40000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-87255986369454329) 6400000000000000000),
            (exactRationalLiteral (241753917294101967) 1600000000000000000),
            (exactRationalLiteral (-20925903460977987) 400000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9839029876417181) 150000000000000000),
            (exactRationalLiteral (-1305999510102321) 8000000000000000),
            (exactRationalLiteral (833491349470867) 5000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (461385333950033003) 6400000000000000000),
            (exactRationalLiteral (13560890921726823) 320000000000000000),
            (exactRationalLiteral (-73859844790024407) 400000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12409362072656053) 800000000000000000),
            (exactRationalLiteral (176273372644707) 8000000000000000),
            (exactRationalLiteral (4776995386943517) 50000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (6442184470601657) 9600000000000000000),
            (exactRationalLiteral (-6751824751973701) 800000000000000000),
            (exactRationalLiteral (-5101067642468671) 200000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6676054165352669) 19200000000000000000),
            (exactRationalLiteral (1993802079441917) 1600000000000000000),
            (exactRationalLiteral (2555794398554467) 400000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (96755277032377213) 19200000000000000000),
            (exactRationalLiteral (2828815595984271) 1600000000000000000),
            (exactRationalLiteral (-792141312400619) 400000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10503126248034043) 2400000000000000000),
            (exactRationalLiteral (1376730072011277) 400000000000000000),
            (exactRationalLiteral (76798903892477) 25000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-103582634239331163) 6400000000000000000),
            (exactRationalLiteral (-8942926783288003) 1600000000000000000),
            (exactRationalLiteral (-1331382186116121) 400000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3618766443630317) 480000000000000000),
            (exactRationalLiteral (-2340988639546409) 400000000000000000),
            (exactRationalLiteral (-32343638610457) 12500000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (73823983782842263) 9600000000000000000),
            (exactRationalLiteral (6737116423947967) 800000000000000000),
            (exactRationalLiteral (903704556329491) 200000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2432094231114601) 4800000000000000000),
            (exactRationalLiteral (818979168017829) 400000000000000000),
            (exactRationalLiteral (-583354085205563) 100000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-107812830796529147) 19200000000000000000),
            (exactRationalLiteral (217578076022039) 64000000000000000),
            (exactRationalLiteral (75111636142573) 400000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (180395005502390561) 9600000000000000000),
            (exactRationalLiteral (-385183216400193) 32000000000000000),
            (exactRationalLiteral (2460330978497) 320000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (295928212106314409) 4800000000000000000),
            (exactRationalLiteral (-3625894343409023) 80000000000000000),
            (exactRationalLiteral (459411698906233) 20000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-158198804621042241) 3200000000000000000),
            (exactRationalLiteral (42324980370999617) 800000000000000000),
            (exactRationalLiteral (-1533564976953579) 40000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-97251193507846091) 3840000000000000000),
            (exactRationalLiteral (8377637271429147) 1600000000000000000),
            (exactRationalLiteral (3173416448803889) 400000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20080977166556963) 4800000000000000000),
            (exactRationalLiteral (-1573577510386837) 400000000000000000),
            (exactRationalLiteral (381358877244517) 100000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1492721070318283697) 9600000000000000000),
            (exactRationalLiteral (68271073471414671) 800000000000000000),
            (exactRationalLiteral (-231312178794989) 8000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3176367257806674139) 9600000000000000000),
            (exactRationalLiteral (-5799393816783539) 32000000000000000),
            (exactRationalLiteral (11678585188574683) 200000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1492721070318283697) 9600000000000000000),
            (exactRationalLiteral (68271073471414671) 800000000000000000),
            (exactRationalLiteral (-231312178794989) 8000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20080977166556963) 4800000000000000000),
            (exactRationalLiteral (-1573577510386837) 400000000000000000),
            (exactRationalLiteral (381358877244517) 100000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-97251193507846091) 3840000000000000000),
            (exactRationalLiteral (8377637271429147) 1600000000000000000),
            (exactRationalLiteral (3173416448803889) 400000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-158198804621042241) 3200000000000000000),
            (exactRationalLiteral (42324980370999617) 800000000000000000),
            (exactRationalLiteral (-1533564976953579) 40000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (295928212106314409) 4800000000000000000),
            (exactRationalLiteral (-3625894343409023) 80000000000000000),
            (exactRationalLiteral (459411698906233) 20000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (180395005502390561) 9600000000000000000),
            (exactRationalLiteral (-385183216400193) 32000000000000000),
            (exactRationalLiteral (2460330978497) 320000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-107812830796529147) 19200000000000000000),
            (exactRationalLiteral (217578076022039) 64000000000000000),
            (exactRationalLiteral (75111636142573) 400000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2432094231114601) 4800000000000000000),
            (exactRationalLiteral (818979168017829) 400000000000000000),
            (exactRationalLiteral (-583354085205563) 100000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (73823983782842263) 9600000000000000000),
            (exactRationalLiteral (6737116423947967) 800000000000000000),
            (exactRationalLiteral (903704556329491) 200000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3618766443630317) 480000000000000000),
            (exactRationalLiteral (-2340988639546409) 400000000000000000),
            (exactRationalLiteral (-32343638610457) 12500000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-103582634239331163) 6400000000000000000),
            (exactRationalLiteral (-8942926783288003) 1600000000000000000),
            (exactRationalLiteral (-1331382186116121) 400000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10503126248034043) 2400000000000000000),
            (exactRationalLiteral (1376730072011277) 400000000000000000),
            (exactRationalLiteral (76798903892477) 25000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (96755277032377213) 19200000000000000000),
            (exactRationalLiteral (2828815595984271) 1600000000000000000),
            (exactRationalLiteral (-792141312400619) 400000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6676054165352669) 19200000000000000000),
            (exactRationalLiteral (1993802079441917) 1600000000000000000),
            (exactRationalLiteral (2555794398554467) 400000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6442184470601657) 9600000000000000000),
            (exactRationalLiteral (-6751824751973701) 800000000000000000),
            (exactRationalLiteral (-5101067642468671) 200000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-12409362072656053) 800000000000000000),
            (exactRationalLiteral (176273372644707) 8000000000000000),
            (exactRationalLiteral (4776995386943517) 50000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (461385333950033003) 6400000000000000000),
            (exactRationalLiteral (13560890921726823) 320000000000000000),
            (exactRationalLiteral (-73859844790024407) 400000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9839029876417181) 150000000000000000),
            (exactRationalLiteral (-1305999510102321) 8000000000000000),
            (exactRationalLiteral (833491349470867) 5000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-87255986369454329) 6400000000000000000),
            (exactRationalLiteral (241753917294101967) 1600000000000000000),
            (exactRationalLiteral (-20925903460977987) 400000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (43074575079375257) 1920000000000000000),
            (exactRationalLiteral (-6745740205839927) 160000000000000000),
            (exactRationalLiteral (-520026768867139) 40000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 9600000000000000000),
            (exactRationalLiteral (-1688946349157141) 800000000000000000),
            (exactRationalLiteral (1688946349157141) 200000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (1688946349157141) 1200000000000000000),
          (exactRationalLiteral (2335099032284573) 75000000000000000),
          (exactRationalLiteral (125309504071407397) 2400000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (49017452903774861) 600000000000000000),
          (exactRationalLiteral (2764585937540659) 150000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (2601931397123) 5000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (83407562212229) 100000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (31297177546484167) 1200000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (456055248181311659) 1200000000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (31297177546484167) 1200000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (83407562212229) 100000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (2601931397123) 5000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (2764585937540659) 150000000000000000),
          (exactRationalLiteral (49017452903774861) 600000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (125309504071407397) 2400000000000000000),
          (exactRationalLiteral (2335099032284573) 75000000000000000),
          (exactRationalLiteral (1688946349157141) 1200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (45, 17),
      (45, 15),
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
      (44, 54)
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
        cell := 6
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
            (exactRationalLiteral (579308597760899363) 76800000000000000000),
            (exactRationalLiteral (-82758371108699909) 3200000000000000000),
            (exactRationalLiteral (11822624444099987) 400000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (424689477179257801) 15360000000000000000),
            (exactRationalLiteral (32747078649196877) 640000000000000000),
            (exactRationalLiteral (-10905954356777039) 80000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-13821840629366760841) 153600000000000000000),
            (exactRationalLiteral (202249018337375783) 6400000000000000000),
            (exactRationalLiteral (194805137089762391) 800000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1014299258150906707) 19200000000000000000),
            (exactRationalLiteral (-4407599179956411) 32000000000000000),
            (exactRationalLiteral (-4150364258336341) 20000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1268277978783836747) 153600000000000000000),
            (exactRationalLiteral (27198396897362963) 256000000000000000),
            (exactRationalLiteral (65971268780141291) 800000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-118003055716629097) 19200000000000000000),
            (exactRationalLiteral (-4689809492985893) 160000000000000000),
            (exactRationalLiteral (-1338713828007001) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-9086404128587903) 25600000000000000000),
            (exactRationalLiteral (18763259221218291) 3200000000000000000),
            (exactRationalLiteral (1048023639114723) 400000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (56053341894242053) 153600000000000000000),
            (exactRationalLiteral (-12284827693403347) 6400000000000000000),
            (exactRationalLiteral (-1059581594874731) 800000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (545618056627217719) 153600000000000000000),
            (exactRationalLiteral (15132894034479639) 6400000000000000000),
            (exactRationalLiteral (820756294692727) 800000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (116415885918479393) 38400000000000000000),
            (exactRationalLiteral (2384942389621923) 1600000000000000000),
            (exactRationalLiteral (10004348544821) 200000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2091169714186882507) 153600000000000000000),
            (exactRationalLiteral (-20733109106270267) 6400000000000000000),
            (exactRationalLiteral (-344955233144107) 800000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12516291149194523) 2560000000000000000),
            (exactRationalLiteral (-4210971622966791) 1600000000000000000),
            (exactRationalLiteral (-513098369276457) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (96759892046232453) 25600000000000000000),
            (exactRationalLiteral (15202552996519323) 3200000000000000000),
            (exactRationalLiteral (541773427195527) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-96043171281862507) 38400000000000000000),
            (exactRationalLiteral (10714610829957601) 1600000000000000000),
            (exactRationalLiteral (-321030661166131) 200000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1443213000135336601) 153600000000000000000),
            (exactRationalLiteral (14675514381927723) 1280000000000000000),
            (exactRationalLiteral (-10474176133772089) 800000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2439292150773224863) 76800000000000000000),
            (exactRationalLiteral (-4272508378207009) 128000000000000000),
            (exactRationalLiteral (2116692767981987) 80000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1296816602189339599) 12800000000000000000),
            (exactRationalLiteral (-27319692652365627) 320000000000000000),
            (exactRationalLiteral (1644399657933441) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-7943224972329715679) 76800000000000000000),
            (exactRationalLiteral (414012640469264493) 3200000000000000000),
            (exactRationalLiteral (-6721378805503483) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-236547738249574099) 10240000000000000000),
            (exactRationalLiteral (-103653266997440717) 6400000000000000000),
            (exactRationalLiteral (21085930319023683) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-695711447278309) 38400000000000000000),
            (exactRationalLiteral (-15588212321495613) 1600000000000000000),
            (exactRationalLiteral (1096062701500619) 200000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-5678577940743842987) 25600000000000000000),
            (exactRationalLiteral (414796419466987259) 3200000000000000000),
            (exactRationalLiteral (-3355363235303253) 80000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (36122371043331111437) 76800000000000000000),
            (exactRationalLiteral (-173124396186617807) 640000000000000000),
            (exactRationalLiteral (33779349473797661) 400000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-5678577940743842987) 25600000000000000000),
            (exactRationalLiteral (414796419466987259) 3200000000000000000),
            (exactRationalLiteral (-3355363235303253) 80000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-695711447278309) 38400000000000000000),
            (exactRationalLiteral (-15588212321495613) 1600000000000000000),
            (exactRationalLiteral (1096062701500619) 200000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-236547738249574099) 10240000000000000000),
            (exactRationalLiteral (-103653266997440717) 6400000000000000000),
            (exactRationalLiteral (21085930319023683) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7943224972329715679) 76800000000000000000),
            (exactRationalLiteral (414012640469264493) 3200000000000000000),
            (exactRationalLiteral (-6721378805503483) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (1296816602189339599) 12800000000000000000),
            (exactRationalLiteral (-27319692652365627) 320000000000000000),
            (exactRationalLiteral (1644399657933441) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (2439292150773224863) 76800000000000000000),
            (exactRationalLiteral (-4272508378207009) 128000000000000000),
            (exactRationalLiteral (2116692767981987) 80000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1443213000135336601) 153600000000000000000),
            (exactRationalLiteral (14675514381927723) 1280000000000000000),
            (exactRationalLiteral (-10474176133772089) 800000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-96043171281862507) 38400000000000000000),
            (exactRationalLiteral (10714610829957601) 1600000000000000000),
            (exactRationalLiteral (-321030661166131) 200000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (96759892046232453) 25600000000000000000),
            (exactRationalLiteral (15202552996519323) 3200000000000000000),
            (exactRationalLiteral (541773427195527) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-12516291149194523) 2560000000000000000),
            (exactRationalLiteral (-4210971622966791) 1600000000000000000),
            (exactRationalLiteral (-513098369276457) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2091169714186882507) 153600000000000000000),
            (exactRationalLiteral (-20733109106270267) 6400000000000000000),
            (exactRationalLiteral (-344955233144107) 800000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (116415885918479393) 38400000000000000000),
            (exactRationalLiteral (2384942389621923) 1600000000000000000),
            (exactRationalLiteral (10004348544821) 200000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (545618056627217719) 153600000000000000000),
            (exactRationalLiteral (15132894034479639) 6400000000000000000),
            (exactRationalLiteral (820756294692727) 800000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (56053341894242053) 153600000000000000000),
            (exactRationalLiteral (-12284827693403347) 6400000000000000000),
            (exactRationalLiteral (-1059581594874731) 800000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9086404128587903) 25600000000000000000),
            (exactRationalLiteral (18763259221218291) 3200000000000000000),
            (exactRationalLiteral (1048023639114723) 400000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-118003055716629097) 19200000000000000000),
            (exactRationalLiteral (-4689809492985893) 160000000000000000),
            (exactRationalLiteral (-1338713828007001) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1268277978783836747) 153600000000000000000),
            (exactRationalLiteral (27198396897362963) 256000000000000000),
            (exactRationalLiteral (65971268780141291) 800000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1014299258150906707) 19200000000000000000),
            (exactRationalLiteral (-4407599179956411) 32000000000000000),
            (exactRationalLiteral (-4150364258336341) 20000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-13821840629366760841) 153600000000000000000),
            (exactRationalLiteral (202249018337375783) 6400000000000000000),
            (exactRationalLiteral (194805137089762391) 800000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (424689477179257801) 15360000000000000000),
            (exactRationalLiteral (32747078649196877) 640000000000000000),
            (exactRationalLiteral (-10905954356777039) 80000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (579308597760899363) 76800000000000000000),
            (exactRationalLiteral (-82758371108699909) 3200000000000000000),
            (exactRationalLiteral (11822624444099987) 400000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (exactRationalLiteral (307616268887703667) 9600000000000000000),
          (exactRationalLiteral (18575815330203441) 200000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (432916670094305603) 19200000000000000000),
          (exactRationalLiteral (23773474834382461) 2400000000000000000),
          (exactRationalLiteral (1221170114801) 1200000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (24708249992951501) 6400000000000000000),
          (exactRationalLiteral (161095837902993) 50000000000000000),
          (exactRationalLiteral (269358433629117907) 19200000000000000000),
          (exactRationalLiteral (1261984107402161) 240000000000000000),
          (exactRationalLiteral (1688828912734673) 384000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (474858237907893221) 19200000000000000000),
          (exactRationalLiteral (193061650824659) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (75825506778068557) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (193061650824659) 150000000000000000),
          (exactRationalLiteral (474858237907893221) 19200000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (1688828912734673) 384000000000000000),
          (exactRationalLiteral (1261984107402161) 240000000000000000),
          (exactRationalLiteral (269358433629117907) 19200000000000000000),
          (exactRationalLiteral (161095837902993) 50000000000000000),
          (exactRationalLiteral (24708249992951501) 6400000000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (1221170114801) 1200000000000000),
          (exactRationalLiteral (23773474834382461) 2400000000000000000),
          (exactRationalLiteral (432916670094305603) 19200000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (18575815330203441) 200000000000000000),
          (exactRationalLiteral (307616268887703667) 9600000000000000000),
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 6),
      (43, 2),
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
      (42, 21)
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
        cell := 6
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
            (exactRationalLiteral (1688946349157141) 614400000000000000),
            (exactRationalLiteral (-1688946349157141) 128000000000000000),
            (exactRationalLiteral (1688946349157141) 80000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2530429690517915063) 76800000000000000000),
            (exactRationalLiteral (-14920090613385351) 3200000000000000000),
            (exactRationalLiteral (-34797970145799673) 400000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-709955732312273789) 10240000000000000000),
            (exactRationalLiteral (158428802297410131) 1280000000000000000),
            (exactRationalLiteral (20028471897015009) 160000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (164012162907023069) 19200000000000000000),
            (exactRationalLiteral (-163259946040757859) 800000000000000000),
            (exactRationalLiteral (-5783161979242087) 100000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1932595735124557507) 51200000000000000000),
            (exactRationalLiteral (154578446173297431) 1280000000000000000),
            (exactRationalLiteral (-19505114563934751) 800000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-85777859693086481) 6400000000000000000),
            (exactRationalLiteral (-20089739095442241) 800000000000000000),
            (exactRationalLiteral (3018368012750613) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (79896372332439409) 76800000000000000000),
            (exactRationalLiteral (13955226638435531) 3200000000000000000),
            (exactRationalLiteral (-3452039930506103) 400000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20496730777500937) 153600000000000000000),
            (exactRationalLiteral (-11586217759315339) 6400000000000000000),
            (exactRationalLiteral (281777312383747) 160000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (642416434099217933) 153600000000000000000),
            (exactRationalLiteral (131935104621243) 51200000000000000),
            (exactRationalLiteral (-141259273104859) 800000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5272504458036031) 1536000000000000000),
            (exactRationalLiteral (2908469289877203) 1600000000000000000),
            (exactRationalLiteral (251759101582819) 200000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-741138775414924803) 51200000000000000000),
            (exactRationalLiteral (-23967177350117203) 6400000000000000000),
            (exactRationalLiteral (-1272078888779361) 800000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-219174417164621443) 38400000000000000000),
            (exactRationalLiteral (-6266884978865303) 1600000000000000000),
            (exactRationalLiteral (-514858308672799) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (390021292340901149) 76800000000000000000),
            (exactRationalLiteral (3676431050734439) 640000000000000000),
            (exactRationalLiteral (1048027701380909) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7392191650180493) 7680000000000000000),
            (exactRationalLiteral (8753946177897081) 1600000000000000000),
            (exactRationalLiteral (-659301664864129) 200000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1111638643233078403) 153600000000000000000),
            (exactRationalLiteral (39980386899396047) 6400000000000000000),
            (exactRationalLiteral (-1244883274269839) 160000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1913404579934230837) 76800000000000000000),
            (exactRationalLiteral (-70485294188966433) 3200000000000000000),
            (exactRationalLiteral (7580243793194461) 400000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3163718396392088647) 38400000000000000000),
            (exactRationalLiteral (-21322555028728643) 320000000000000000),
            (exactRationalLiteral (1354169153885051) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-1944399289010522367) 25600000000000000000),
            (exactRationalLiteral (294202059765580133) 3200000000000000000),
            (exactRationalLiteral (-5259679264864953) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-3940687067774237039) 153600000000000000000),
            (exactRationalLiteral (-31100823658478709) 6400000000000000000),
            (exactRationalLiteral (15190291350457321) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16321116974692619) 7680000000000000000),
            (exactRationalLiteral (-2294127494620481) 320000000000000000),
            (exactRationalLiteral (192544944539197) 40000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-14739939167968973683) 76800000000000000000),
            (exactRationalLiteral (351858120550335651) 3200000000000000000),
            (exactRationalLiteral (-14692333281809539) 400000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (31317315864863511887) 76800000000000000000),
            (exactRationalLiteral (-738842326315217027) 3200000000000000000),
            (exactRationalLiteral (29610477835138343) 400000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14739939167968973683) 76800000000000000000),
            (exactRationalLiteral (351858120550335651) 3200000000000000000),
            (exactRationalLiteral (-14692333281809539) 400000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-16321116974692619) 7680000000000000000),
            (exactRationalLiteral (-2294127494620481) 320000000000000000),
            (exactRationalLiteral (192544944539197) 40000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3940687067774237039) 153600000000000000000),
            (exactRationalLiteral (-31100823658478709) 6400000000000000000),
            (exactRationalLiteral (15190291350457321) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1944399289010522367) 25600000000000000000),
            (exactRationalLiteral (294202059765580133) 3200000000000000000),
            (exactRationalLiteral (-5259679264864953) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (3163718396392088647) 38400000000000000000),
            (exactRationalLiteral (-21322555028728643) 320000000000000000),
            (exactRationalLiteral (1354169153885051) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (1913404579934230837) 76800000000000000000),
            (exactRationalLiteral (-70485294188966433) 3200000000000000000),
            (exactRationalLiteral (7580243793194461) 400000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1111638643233078403) 153600000000000000000),
            (exactRationalLiteral (39980386899396047) 6400000000000000000),
            (exactRationalLiteral (-1244883274269839) 160000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-7392191650180493) 7680000000000000000),
            (exactRationalLiteral (8753946177897081) 1600000000000000000),
            (exactRationalLiteral (-659301664864129) 200000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (390021292340901149) 76800000000000000000),
            (exactRationalLiteral (3676431050734439) 640000000000000000),
            (exactRationalLiteral (1048027701380909) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-219174417164621443) 38400000000000000000),
            (exactRationalLiteral (-6266884978865303) 1600000000000000000),
            (exactRationalLiteral (-514858308672799) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-741138775414924803) 51200000000000000000),
            (exactRationalLiteral (-23967177350117203) 6400000000000000000),
            (exactRationalLiteral (-1272078888779361) 800000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5272504458036031) 1536000000000000000),
            (exactRationalLiteral (2908469289877203) 1600000000000000000),
            (exactRationalLiteral (251759101582819) 200000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (642416434099217933) 153600000000000000000),
            (exactRationalLiteral (131935104621243) 51200000000000000),
            (exactRationalLiteral (-141259273104859) 800000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20496730777500937) 153600000000000000000),
            (exactRationalLiteral (-11586217759315339) 6400000000000000000),
            (exactRationalLiteral (281777312383747) 160000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (79896372332439409) 76800000000000000000),
            (exactRationalLiteral (13955226638435531) 3200000000000000000),
            (exactRationalLiteral (-3452039930506103) 400000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-85777859693086481) 6400000000000000000),
            (exactRationalLiteral (-20089739095442241) 800000000000000000),
            (exactRationalLiteral (3018368012750613) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1932595735124557507) 51200000000000000000),
            (exactRationalLiteral (154578446173297431) 1280000000000000000),
            (exactRationalLiteral (-19505114563934751) 800000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (164012162907023069) 19200000000000000000),
            (exactRationalLiteral (-163259946040757859) 800000000000000000),
            (exactRationalLiteral (-5783161979242087) 100000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-709955732312273789) 10240000000000000000),
            (exactRationalLiteral (158428802297410131) 1280000000000000000),
            (exactRationalLiteral (20028471897015009) 160000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2530429690517915063) 76800000000000000000),
            (exactRationalLiteral (-14920090613385351) 3200000000000000000),
            (exactRationalLiteral (-34797970145799673) 400000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 614400000000000000),
            (exactRationalLiteral (-1688946349157141) 128000000000000000),
            (exactRationalLiteral (1688946349157141) 80000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (15200517142414269) 3200000000000000000),
          (exactRationalLiteral (1686206804750093) 50000000000000000),
          (exactRationalLiteral (1584751193985961249) 19200000000000000000),
          (exactRationalLiteral (13103295529903137) 400000000000000000),
          (exactRationalLiteral (125237661915770183) 2400000000000000000),
          (exactRationalLiteral (59837724884171) 3750000000000000),
          (exactRationalLiteral (113704063199393) 80000000000000000),
          (exactRationalLiteral (778038910801469) 2400000000000000000),
          (exactRationalLiteral (10796676761390167) 2400000000000000000),
          (exactRationalLiteral (883838587511249) 240000000000000000),
          (exactRationalLiteral (35931213387332527) 2400000000000000000),
          (exactRationalLiteral (499001097910279) 80000000000000000),
          (exactRationalLiteral (292034484598407) 50000000000000000),
          (exactRationalLiteral (8128945784667137) 4800000000000000000),
          (exactRationalLiteral (156547241615815697) 19200000000000000000),
          (exactRationalLiteral (268637850488008907) 9600000000000000000),
          (exactRationalLiteral (438074354423926879) 4800000000000000000),
          (exactRationalLiteral (169958837103821953) 1920000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (1980079096364095327) 9600000000000000000),
          (exactRationalLiteral (4203094839141738457) 9600000000000000000),
          (exactRationalLiteral (1980079096364095327) 9600000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (169958837103821953) 1920000000000000000),
          (exactRationalLiteral (438074354423926879) 4800000000000000000),
          (exactRationalLiteral (268637850488008907) 9600000000000000000),
          (exactRationalLiteral (156547241615815697) 19200000000000000000),
          (exactRationalLiteral (8128945784667137) 4800000000000000000),
          (exactRationalLiteral (292034484598407) 50000000000000000),
          (exactRationalLiteral (499001097910279) 80000000000000000),
          (exactRationalLiteral (35931213387332527) 2400000000000000000),
          (exactRationalLiteral (883838587511249) 240000000000000000),
          (exactRationalLiteral (10796676761390167) 2400000000000000000),
          (exactRationalLiteral (778038910801469) 2400000000000000000),
          (exactRationalLiteral (113704063199393) 80000000000000000),
          (exactRationalLiteral (59837724884171) 3750000000000000),
          (exactRationalLiteral (125237661915770183) 2400000000000000000),
          (exactRationalLiteral (13103295529903137) 400000000000000000),
          (exactRationalLiteral (1584751193985961249) 19200000000000000000),
          (exactRationalLiteral (1686206804750093) 50000000000000000),
          (exactRationalLiteral (15200517142414269) 3200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 7),
      (43, 3),
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
      (42, 20)
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
        cell := 6
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
            (exactRationalLiteral (15200517142414269) 25600000000000000000),
            (exactRationalLiteral (-15200517142414269) 3200000000000000000),
            (exactRationalLiteral (5066839047471423) 400000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2102260711640348969) 76800000000000000000),
            (exactRationalLiteral (-114648367920412999) 3200000000000000000),
            (exactRationalLiteral (-15066168507714151) 400000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-5073414712359651749) 153600000000000000000),
            (exactRationalLiteral (1003387894217976143) 6400000000000000000),
            (exactRationalLiteral (5479581880387699) 800000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-275023606612890219) 6400000000000000000),
            (exactRationalLiteral (-156455275332846971) 800000000000000000),
            (exactRationalLiteral (9185497333197531) 100000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (9859173682429074271) 153600000000000000000),
            (exactRationalLiteral (523919005922596067) 6400000000000000000),
            (exactRationalLiteral (-104981497908010793) 800000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-324223270135875077) 19200000000000000000),
            (exactRationalLiteral (697896637075439) 800000000000000000),
            (exactRationalLiteral (7375449853508227) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (20840599743699211) 15360000000000000000),
            (exactRationalLiteral (-8853060222830533) 3200000000000000000),
            (exactRationalLiteral (-7952103500126929) 400000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-21077841987731429) 51200000000000000000),
            (exactRationalLiteral (-1013735198053467) 6400000000000000000),
            (exactRationalLiteral (3877354718712201) 800000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (245274863005567177) 51200000000000000000),
            (exactRationalLiteral (14002819849640767) 6400000000000000000),
            (exactRationalLiteral (-220654968180489) 160000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (51083851807103271) 12800000000000000000),
            (exactRationalLiteral (175960608091379) 64000000000000000),
            (exactRationalLiteral (493513854620817) 200000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-95447713265334839) 6144000000000000000),
            (exactRationalLiteral (-6181948043301031) 1280000000000000000),
            (exactRationalLiteral (-439840508882923) 160000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-262961066499472217) 38400000000000000000),
            (exactRationalLiteral (-8329838092349183) 1600000000000000000),
            (exactRationalLiteral (-516618248069141) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (102983114675249351) 15360000000000000000),
            (exactRationalLiteral (4717354921513319) 640000000000000000),
            (exactRationalLiteral (1554281975566291) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6298014823318481) 38400000000000000000),
            (exactRationalLiteral (5440197511044569) 1600000000000000000),
            (exactRationalLiteral (-997572668562127) 200000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-185890055848640177) 30720000000000000000),
            (exactRationalLiteral (4716448187769011) 1280000000000000000),
            (exactRationalLiteral (-1974656608926301) 800000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (12555542881055231) 614400000000000000),
            (exactRationalLiteral (-46170759109619537) 3200000000000000000),
            (exactRationalLiteral (4577023746478987) 400000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2599487284682364617) 38400000000000000000),
            (exactRationalLiteral (-16486339421285219) 320000000000000000),
            (exactRationalLiteral (1063938649836661) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-4354332273517212883) 76800000000000000000),
            (exactRationalLiteral (203625469874666373) 3200000000000000000),
            (exactRationalLiteral (-3797979724226423) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-3968591069393886889) 153600000000000000000),
            (exactRationalLiteral (17869063806217851) 6400000000000000000),
            (exactRationalLiteral (9294652381890959) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-139410064954944241) 38400000000000000000),
            (exactRationalLiteral (-7886414539927733) 1600000000000000000),
            (exactRationalLiteral (829386743891351) 200000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-12796760512469847341) 76800000000000000000),
            (exactRationalLiteral (297257753212510947) 3200000000000000000),
            (exactRationalLiteral (-12607850387102813) 400000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27222912154439232569) 76800000000000000000),
            (exactRationalLiteral (-628738158251982291) 3200000000000000000),
            (exactRationalLiteral (1017664247859161) 16000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-12796760512469847341) 76800000000000000000),
            (exactRationalLiteral (297257753212510947) 3200000000000000000),
            (exactRationalLiteral (-12607850387102813) 400000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-139410064954944241) 38400000000000000000),
            (exactRationalLiteral (-7886414539927733) 1600000000000000000),
            (exactRationalLiteral (829386743891351) 200000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3968591069393886889) 153600000000000000000),
            (exactRationalLiteral (17869063806217851) 6400000000000000000),
            (exactRationalLiteral (9294652381890959) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4354332273517212883) 76800000000000000000),
            (exactRationalLiteral (203625469874666373) 3200000000000000000),
            (exactRationalLiteral (-3797979724226423) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (2599487284682364617) 38400000000000000000),
            (exactRationalLiteral (-16486339421285219) 320000000000000000),
            (exactRationalLiteral (1063938649836661) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (12555542881055231) 614400000000000000),
            (exactRationalLiteral (-46170759109619537) 3200000000000000000),
            (exactRationalLiteral (4577023746478987) 400000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-185890055848640177) 30720000000000000000),
            (exactRationalLiteral (4716448187769011) 1280000000000000000),
            (exactRationalLiteral (-1974656608926301) 800000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (6298014823318481) 38400000000000000000),
            (exactRationalLiteral (5440197511044569) 1600000000000000000),
            (exactRationalLiteral (-997572668562127) 200000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (102983114675249351) 15360000000000000000),
            (exactRationalLiteral (4717354921513319) 640000000000000000),
            (exactRationalLiteral (1554281975566291) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-262961066499472217) 38400000000000000000),
            (exactRationalLiteral (-8329838092349183) 1600000000000000000),
            (exactRationalLiteral (-516618248069141) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-95447713265334839) 6144000000000000000),
            (exactRationalLiteral (-6181948043301031) 1280000000000000000),
            (exactRationalLiteral (-439840508882923) 160000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (51083851807103271) 12800000000000000000),
            (exactRationalLiteral (175960608091379) 64000000000000000),
            (exactRationalLiteral (493513854620817) 200000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (245274863005567177) 51200000000000000000),
            (exactRationalLiteral (14002819849640767) 6400000000000000000),
            (exactRationalLiteral (-220654968180489) 160000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-21077841987731429) 51200000000000000000),
            (exactRationalLiteral (-1013735198053467) 6400000000000000000),
            (exactRationalLiteral (3877354718712201) 800000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (20840599743699211) 15360000000000000000),
            (exactRationalLiteral (-8853060222830533) 3200000000000000000),
            (exactRationalLiteral (-7952103500126929) 400000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-324223270135875077) 19200000000000000000),
            (exactRationalLiteral (697896637075439) 800000000000000000),
            (exactRationalLiteral (7375449853508227) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (9859173682429074271) 153600000000000000000),
            (exactRationalLiteral (523919005922596067) 6400000000000000000),
            (exactRationalLiteral (-104981497908010793) 800000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-275023606612890219) 6400000000000000000),
            (exactRationalLiteral (-156455275332846971) 800000000000000000),
            (exactRationalLiteral (9185497333197531) 100000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-5073414712359651749) 153600000000000000000),
            (exactRationalLiteral (1003387894217976143) 6400000000000000000),
            (exactRationalLiteral (5479581880387699) 800000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2102260711640348969) 76800000000000000000),
            (exactRationalLiteral (-114648367920412999) 3200000000000000000),
            (exactRationalLiteral (-15066168507714151) 400000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15200517142414269) 25600000000000000000),
            (exactRationalLiteral (-15200517142414269) 3200000000000000000),
            (exactRationalLiteral (5066839047471423) 400000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (1688946349157141) 1200000000000000000),
          (exactRationalLiteral (2335099032284573) 75000000000000000),
          (exactRationalLiteral (125309504071407397) 2400000000000000000),
          (exactRationalLiteral (9839029876417181) 150000000000000000),
          (exactRationalLiteral (461385333950033003) 6400000000000000000),
          (exactRationalLiteral (6939153422347639) 400000000000000000),
          (exactRationalLiteral (1237063861006699) 800000000000000000),
          (exactRationalLiteral (4334928122397293) 9600000000000000000),
          (exactRationalLiteral (96755277032377213) 19200000000000000000),
          (exactRationalLiteral (10503126248034043) 2400000000000000000),
          (exactRationalLiteral (103582634239331163) 6400000000000000000),
          (exactRationalLiteral (3618766443630317) 480000000000000000),
          (exactRationalLiteral (73823983782842263) 9600000000000000000),
          (exactRationalLiteral (2432094231114601) 4800000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (24991891281664243) 960000000000000000),
          (exactRationalLiteral (20080977166556963) 4800000000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (456055248181311659) 1200000000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (20080977166556963) 4800000000000000000),
          (exactRationalLiteral (24991891281664243) 960000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (2432094231114601) 4800000000000000000),
          (exactRationalLiteral (73823983782842263) 9600000000000000000),
          (exactRationalLiteral (3618766443630317) 480000000000000000),
          (exactRationalLiteral (103582634239331163) 6400000000000000000),
          (exactRationalLiteral (10503126248034043) 2400000000000000000),
          (exactRationalLiteral (96755277032377213) 19200000000000000000),
          (exactRationalLiteral (4334928122397293) 9600000000000000000),
          (exactRationalLiteral (1237063861006699) 800000000000000000),
          (exactRationalLiteral (6939153422347639) 400000000000000000),
          (exactRationalLiteral (461385333950033003) 6400000000000000000),
          (exactRationalLiteral (9839029876417181) 150000000000000000),
          (exactRationalLiteral (125309504071407397) 2400000000000000000),
          (exactRationalLiteral (2335099032284573) 75000000000000000),
          (exactRationalLiteral (1688946349157141) 1200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 8),
      (43, 4),
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
      (42, 19)
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
        cell := 6
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
            (exactRationalLiteral (1688946349157141) 76800000000000000000),
            (exactRationalLiteral (-1688946349157141) 3200000000000000000),
            (exactRationalLiteral (1688946349157141) 400000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1312503688577643251) 76800000000000000000),
            (exactRationalLiteral (-135449438675098559) 3200000000000000000),
            (exactRationalLiteral (4665633130371371) 400000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (634016525094108113) 153600000000000000000),
            (exactRationalLiteral (835980666530152247) 6400000000000000000),
            (exactRationalLiteral (-89183195724299647) 800000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1593701866587623639) 19200000000000000000),
            (exactRationalLiteral (-89775967375177611) 800000000000000000),
            (exactRationalLiteral (24154156645637149) 100000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (11401004209692216989) 153600000000000000000),
            (exactRationalLiteral (-66959752397599189) 6400000000000000000),
            (exactRationalLiteral (-38091576250417367) 160000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-214102164708293263) 19200000000000000000),
            (exactRationalLiteral (1556554389304943) 32000000000000000),
            (exactRationalLiteral (11732531694265841) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-4156057259899573) 5120000000000000000),
            (exactRationalLiteral (-49661601362579901) 3200000000000000000),
            (exactRationalLiteral (-2490433413949551) 80000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-12913807899794813) 153600000000000000000),
            (exactRationalLiteral (19432619990382269) 6400000000000000000),
            (exactRationalLiteral (6345822875505667) 800000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (802754147752526449) 153600000000000000000),
            (exactRationalLiteral (1533137870087163) 1280000000000000000),
            (exactRationalLiteral (-2065290408700031) 800000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (186534831902618459) 38400000000000000000),
            (exactRationalLiteral (6856580126843739) 1600000000000000000),
            (exactRationalLiteral (147053721531763) 40000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2601750198087918301) 153600000000000000000),
            (exactRationalLiteral (-41560797705434123) 6400000000000000000),
            (exactRationalLiteral (-3126326200049869) 800000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-851057476767953) 102400000000000000),
            (exactRationalLiteral (-10399830963418431) 1600000000000000000),
            (exactRationalLiteral (-518378187465483) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (45140841455012223) 5120000000000000000),
            (exactRationalLiteral (30816411058202523) 3200000000000000000),
            (exactRationalLiteral (2060536249751673) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (25615243852048379) 38400000000000000000),
            (exactRationalLiteral (154672965880013) 320000000000000000),
            (exactRationalLiteral (-10686749378081) 1600000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-794653673867554591) 153600000000000000000),
            (exactRationalLiteral (24183134027985639) 6400000000000000000),
            (exactRationalLiteral (2275103153496593) 800000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1335329710245072601) 76800000000000000000),
            (exactRationalLiteral (-33869104217134537) 3200000000000000000),
            (exactRationalLiteral (1573803699763513) 400000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (720976270317679969) 12800000000000000000),
            (exactRationalLiteral (-2562209166007071) 64000000000000000),
            (exactRationalLiteral (773708145788271) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-133248969876401177) 3072000000000000000),
            (exactRationalLiteral (142282870796523213) 3200000000000000000),
            (exactRationalLiteral (-2336280183587893) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-1257807804616051241) 51200000000000000000),
            (exactRationalLiteral (43256395396648963) 6400000000000000000),
            (exactRationalLiteral (3399013413324597) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-177309263183032963) 38400000000000000000),
            (exactRationalLiteral (-4835543521971597) 1600000000000000000),
            (exactRationalLiteral (696048765086717) 200000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3718723422087062837) 25600000000000000000),
            (exactRationalLiteral (250995317453513147) 3200000000000000000),
            (exactRationalLiteral (-10523367492396087) 400000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (23739106992730449851) 76800000000000000000),
            (exactRationalLiteral (-535309476743384827) 3200000000000000000),
            (exactRationalLiteral (21272734557819707) 400000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3718723422087062837) 25600000000000000000),
            (exactRationalLiteral (250995317453513147) 3200000000000000000),
            (exactRationalLiteral (-10523367492396087) 400000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-177309263183032963) 38400000000000000000),
            (exactRationalLiteral (-4835543521971597) 1600000000000000000),
            (exactRationalLiteral (696048765086717) 200000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1257807804616051241) 51200000000000000000),
            (exactRationalLiteral (43256395396648963) 6400000000000000000),
            (exactRationalLiteral (3399013413324597) 800000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-133248969876401177) 3072000000000000000),
            (exactRationalLiteral (142282870796523213) 3200000000000000000),
            (exactRationalLiteral (-2336280183587893) 80000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (720976270317679969) 12800000000000000000),
            (exactRationalLiteral (-2562209166007071) 64000000000000000),
            (exactRationalLiteral (773708145788271) 40000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (1335329710245072601) 76800000000000000000),
            (exactRationalLiteral (-33869104217134537) 3200000000000000000),
            (exactRationalLiteral (1573803699763513) 400000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-794653673867554591) 153600000000000000000),
            (exactRationalLiteral (24183134027985639) 6400000000000000000),
            (exactRationalLiteral (2275103153496593) 800000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (25615243852048379) 38400000000000000000),
            (exactRationalLiteral (154672965880013) 320000000000000000),
            (exactRationalLiteral (-10686749378081) 1600000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (45140841455012223) 5120000000000000000),
            (exactRationalLiteral (30816411058202523) 3200000000000000000),
            (exactRationalLiteral (2060536249751673) 400000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-851057476767953) 102400000000000000),
            (exactRationalLiteral (-10399830963418431) 1600000000000000000),
            (exactRationalLiteral (-518378187465483) 200000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2601750198087918301) 153600000000000000000),
            (exactRationalLiteral (-41560797705434123) 6400000000000000000),
            (exactRationalLiteral (-3126326200049869) 800000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (186534831902618459) 38400000000000000000),
            (exactRationalLiteral (6856580126843739) 1600000000000000000),
            (exactRationalLiteral (147053721531763) 40000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (802754147752526449) 153600000000000000000),
            (exactRationalLiteral (1533137870087163) 1280000000000000000),
            (exactRationalLiteral (-2065290408700031) 800000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12913807899794813) 153600000000000000000),
            (exactRationalLiteral (19432619990382269) 6400000000000000000),
            (exactRationalLiteral (6345822875505667) 800000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4156057259899573) 5120000000000000000),
            (exactRationalLiteral (-49661601362579901) 3200000000000000000),
            (exactRationalLiteral (-2490433413949551) 80000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-214102164708293263) 19200000000000000000),
            (exactRationalLiteral (1556554389304943) 32000000000000000),
            (exactRationalLiteral (11732531694265841) 100000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (11401004209692216989) 153600000000000000000),
            (exactRationalLiteral (-66959752397599189) 6400000000000000000),
            (exactRationalLiteral (-38091576250417367) 160000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1593701866587623639) 19200000000000000000),
            (exactRationalLiteral (-89775967375177611) 800000000000000000),
            (exactRationalLiteral (24154156645637149) 100000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (634016525094108113) 153600000000000000000),
            (exactRationalLiteral (835980666530152247) 6400000000000000000),
            (exactRationalLiteral (-89183195724299647) 800000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1312503688577643251) 76800000000000000000),
            (exactRationalLiteral (-135449438675098559) 3200000000000000000),
            (exactRationalLiteral (4665633130371371) 400000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 76800000000000000000),
            (exactRationalLiteral (-1688946349157141) 3200000000000000000),
            (exactRationalLiteral (1688946349157141) 400000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (1688946349157141) 9600000000000000000),
          (exactRationalLiteral (43074575079375257) 1920000000000000000),
          (exactRationalLiteral (1104327167464579) 60000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (120996704704894427) 1600000000000000000),
          (exactRationalLiteral (12409362072656053) 800000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (21372316007899) 50000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (435837310243087) 600000000000000000),
          (exactRationalLiteral (107812830796529147) 19200000000000000000),
          (exactRationalLiteral (180395005502390561) 9600000000000000000),
          (exactRationalLiteral (295928212106314409) 4800000000000000000),
          (exactRationalLiteral (158198804621042241) 3200000000000000000),
          (exactRationalLiteral (97251193507846091) 3840000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (1492721070318283697) 9600000000000000000),
          (exactRationalLiteral (3176367257806674139) 9600000000000000000),
          (exactRationalLiteral (1492721070318283697) 9600000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (97251193507846091) 3840000000000000000),
          (exactRationalLiteral (158198804621042241) 3200000000000000000),
          (exactRationalLiteral (295928212106314409) 4800000000000000000),
          (exactRationalLiteral (180395005502390561) 9600000000000000000),
          (exactRationalLiteral (107812830796529147) 19200000000000000000),
          (exactRationalLiteral (435837310243087) 600000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (21372316007899) 50000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (12409362072656053) 800000000000000000),
          (exactRationalLiteral (120996704704894427) 1600000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (1104327167464579) 60000000000000000),
          (exactRationalLiteral (43074575079375257) 1920000000000000000),
          (exactRationalLiteral (1688946349157141) 9600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 9),
      (43, 5),
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
      (42, 18)
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
        cell := 6
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
            (exactRationalLiteral (15200517142414269) 1638400000000000000),
            (exactRationalLiteral (-15200517142414269) 512000000000000000),
            (exactRationalLiteral (5066839047471423) 160000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (14685709836696145489) 614400000000000000000),
            (exactRationalLiteral (882926560938521081) 12800000000000000000),
            (exactRationalLiteral (-118925444386813151) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-22357110208728335621) 245760000000000000000),
            (exactRationalLiteral (-3511172762378021) 5120000000000000000),
            (exactRationalLiteral (87388332596373691) 320000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3101559520595955639) 51200000000000000000),
            (exactRationalLiteral (-350268303172694471) 3200000000000000000),
            (exactRationalLiteral (-48987972239583219) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2425270565414690843) 1228800000000000000000),
            (exactRationalLiteral (482643284588738623) 5120000000000000000),
            (exactRationalLiteral (174680729232320603) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-672846700042300009) 153600000000000000000),
            (exactRationalLiteral (-86262793627311049) 3200000000000000000),
            (exactRationalLiteral (-4855968576392809) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-434694636121230413) 614400000000000000000),
            (exactRationalLiteral (68610910543603859) 12800000000000000000),
            (exactRationalLiteral (4346079063039859) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (196084314609043823) 409600000000000000000),
            (exactRationalLiteral (-43666750315717731) 25600000000000000000),
            (exactRationalLiteral (-670679453629239) 320000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1396251756718680413) 409600000000000000000),
            (exactRationalLiteral (11353508635049771) 5120000000000000000),
            (exactRationalLiteral (2122520373284247) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (60176461825808133) 20480000000000000000),
            (exactRationalLiteral (9620629540827407) 6400000000000000000),
            (exactRationalLiteral (-100868679429357) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-16482166573790863867) 1228800000000000000000),
            (exactRationalLiteral (-82016177320322267) 25600000000000000000),
            (exactRationalLiteral (-226348638470587) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1454500988673701839) 307200000000000000000),
            (exactRationalLiteral (-14792372984459507) 6400000000000000000),
            (exactRationalLiteral (-1025316768854743) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2142804286577427467) 614400000000000000000),
            (exactRationalLiteral (471169963315103) 102400000000000000),
            (exactRationalLiteral (830419717298363) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-179735549735907811) 61440000000000000000),
            (exactRationalLiteral (43973430462645929) 6400000000000000000),
            (exactRationalLiteral (-472925820483263) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-12491204800682200169) 1228800000000000000000),
            (exactRationalLiteral (337531872054854263) 25600000000000000000),
            (exactRationalLiteral (-36917171438009) 2560000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (20861092112710718951) 614400000000000000000),
            (exactRationalLiteral (-471086303203698377) 12800000000000000000),
            (exactRationalLiteral (22668537703177607) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (32812837577684212201) 307200000000000000000),
            (exactRationalLiteral (-116001484493220467) 1280000000000000000),
            (exactRationalLiteral (3433914567891077) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-68719247077285600163) 614400000000000000000),
            (exactRationalLiteral (1794132386838723957) 12800000000000000000),
            (exactRationalLiteral (-14173607381326231) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-27012425984581177997) 1228800000000000000000),
            (exactRationalLiteral (-501904608750140781) 25600000000000000000),
            (exactRationalLiteral (45119680122330547) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (37627180295625383) 61440000000000000000),
            (exactRationalLiteral (-13360753816277449) 1280000000000000000),
            (exactRationalLiteral (451758878480711) 80000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-141365130749962529749) 614400000000000000000),
            (exactRationalLiteral (1727335184021367459) 12800000000000000000),
            (exactRationalLiteral (-34595873800385893) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (299571192650508075541) 614400000000000000000),
            (exactRationalLiteral (-3599689757446876443) 12800000000000000000),
            (exactRationalLiteral (69643134766924981) 800000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-141365130749962529749) 614400000000000000000),
            (exactRationalLiteral (1727335184021367459) 12800000000000000000),
            (exactRationalLiteral (-34595873800385893) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (37627180295625383) 61440000000000000000),
            (exactRationalLiteral (-13360753816277449) 1280000000000000000),
            (exactRationalLiteral (451758878480711) 80000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-27012425984581177997) 1228800000000000000000),
            (exactRationalLiteral (-501904608750140781) 25600000000000000000),
            (exactRationalLiteral (45119680122330547) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-68719247077285600163) 614400000000000000000),
            (exactRationalLiteral (1794132386838723957) 12800000000000000000),
            (exactRationalLiteral (-14173607381326231) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (32812837577684212201) 307200000000000000000),
            (exactRationalLiteral (-116001484493220467) 1280000000000000000),
            (exactRationalLiteral (3433914567891077) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (20861092112710718951) 614400000000000000000),
            (exactRationalLiteral (-471086303203698377) 12800000000000000000),
            (exactRationalLiteral (22668537703177607) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-12491204800682200169) 1228800000000000000000),
            (exactRationalLiteral (337531872054854263) 25600000000000000000),
            (exactRationalLiteral (-36917171438009) 2560000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-179735549735907811) 61440000000000000000),
            (exactRationalLiteral (43973430462645929) 6400000000000000000),
            (exactRationalLiteral (-472925820483263) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2142804286577427467) 614400000000000000000),
            (exactRationalLiteral (471169963315103) 102400000000000000),
            (exactRationalLiteral (830419717298363) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1454500988673701839) 307200000000000000000),
            (exactRationalLiteral (-14792372984459507) 6400000000000000000),
            (exactRationalLiteral (-1025316768854743) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-16482166573790863867) 1228800000000000000000),
            (exactRationalLiteral (-82016177320322267) 25600000000000000000),
            (exactRationalLiteral (-226348638470587) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (60176461825808133) 20480000000000000000),
            (exactRationalLiteral (9620629540827407) 6400000000000000000),
            (exactRationalLiteral (-100868679429357) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1396251756718680413) 409600000000000000000),
            (exactRationalLiteral (11353508635049771) 5120000000000000000),
            (exactRationalLiteral (2122520373284247) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (196084314609043823) 409600000000000000000),
            (exactRationalLiteral (-43666750315717731) 25600000000000000000),
            (exactRationalLiteral (-670679453629239) 320000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-434694636121230413) 614400000000000000000),
            (exactRationalLiteral (68610910543603859) 12800000000000000000),
            (exactRationalLiteral (4346079063039859) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-672846700042300009) 153600000000000000000),
            (exactRationalLiteral (-86262793627311049) 3200000000000000000),
            (exactRationalLiteral (-4855968576392809) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2425270565414690843) 1228800000000000000000),
            (exactRationalLiteral (482643284588738623) 5120000000000000000),
            (exactRationalLiteral (174680729232320603) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3101559520595955639) 51200000000000000000),
            (exactRationalLiteral (-350268303172694471) 3200000000000000000),
            (exactRationalLiteral (-48987972239583219) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-22357110208728335621) 245760000000000000000),
            (exactRationalLiteral (-3511172762378021) 5120000000000000000),
            (exactRationalLiteral (87388332596373691) 320000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14685709836696145489) 614400000000000000000),
            (exactRationalLiteral (882926560938521081) 12800000000000000000),
            (exactRationalLiteral (-118925444386813151) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15200517142414269) 1638400000000000000),
            (exactRationalLiteral (-15200517142414269) 512000000000000000),
            (exactRationalLiteral (5066839047471423) 160000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
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
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (exactRationalLiteral (424689477179257801) 15360000000000000000),
          (exactRationalLiteral (36540451898311849) 400000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (1268277978783836747) 153600000000000000000),
          (exactRationalLiteral (118003055716629097) 19200000000000000000),
          (exactRationalLiteral (1221170114801) 1200000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (545618056627217719) 153600000000000000000),
          (exactRationalLiteral (116415885918479393) 38400000000000000000),
          (exactRationalLiteral (2091169714186882507) 153600000000000000000),
          (exactRationalLiteral (12516291149194523) 2560000000000000000),
          (exactRationalLiteral (96759892046232453) 25600000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (236547738249574099) 10240000000000000000),
          (exactRationalLiteral (193061650824659) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (75825506778068557) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (193061650824659) 150000000000000000),
          (exactRationalLiteral (236547738249574099) 10240000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (96759892046232453) 25600000000000000000),
          (exactRationalLiteral (12516291149194523) 2560000000000000000),
          (exactRationalLiteral (2091169714186882507) 153600000000000000000),
          (exactRationalLiteral (116415885918479393) 38400000000000000000),
          (exactRationalLiteral (545618056627217719) 153600000000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (1221170114801) 1200000000000000),
          (exactRationalLiteral (118003055716629097) 19200000000000000000),
          (exactRationalLiteral (1268277978783836747) 153600000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (36540451898311849) 400000000000000000),
          (exactRationalLiteral (424689477179257801) 15360000000000000000),
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (38, 52),
      (38, 44),
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
      (37, 19)
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
theorem generatorCoordinates25_valid : ∀ i, (generatorCoordinates25 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
