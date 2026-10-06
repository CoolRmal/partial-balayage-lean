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

/-- Actual coordinate interval candidates, block 29. -/
def generatorCoordinates29 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 7
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 6400000000000000000),
            (exactRationalLiteral (-32695951386181797) 1600000000000000000),
            (exactRationalLiteral (10898650462060599) 400000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7839420388222457) 240000000000000000),
            (exactRationalLiteral (368847865928483) 16000000000000000),
            (exactRationalLiteral (-1185716067840809) 10000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-55214453694390111) 640000000000000000),
            (exactRationalLiteral (13602871079162807) 160000000000000000),
            (exactRationalLiteral (38720707219783623) 200000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (222240998353277563) 6400000000000000000),
            (exactRationalLiteral (-58924750965017911) 320000000000000000),
            (exactRationalLiteral (-55372291719574407) 400000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (150305125865855617) 6400000000000000000),
            (exactRationalLiteral (197025680480098211) 1600000000000000000),
            (exactRationalLiteral (12266461938451491) 400000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8506360635618461) 800000000000000000),
            (exactRationalLiteral (-1559420003697729) 50000000000000000),
            (exactRationalLiteral (401092797459219) 50000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (264127484437433) 128000000000000000),
            (exactRationalLiteral (5471437465867683) 800000000000000000),
            (exactRationalLiteral (-593389250081709) 200000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (51187784528156153) 9600000000000000000),
            (exactRationalLiteral (-131312160593069) 800000000000000000),
            (exactRationalLiteral (123499793914517) 200000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4213225472049163) 600000000000000000),
            (exactRationalLiteral (2874826489633573) 400000000000000000),
            (exactRationalLiteral (167377408937287) 50000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-63783844457141047) 3200000000000000000),
            (exactRationalLiteral (-7367612654106651) 800000000000000000),
            (exactRationalLiteral (-435514155470841) 200000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-71786423775515093) 6400000000000000000),
            (exactRationalLiteral (-15494789790956691) 1600000000000000000),
            (exactRationalLiteral (-603761233716363) 80000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (127114631967087491) 9600000000000000000),
            (exactRationalLiteral (11362921065498701) 800000000000000000),
            (exactRationalLiteral (1408436698376879) 200000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1621912189971497) 19200000000000000000),
            (exactRationalLiteral (-6356373718624481) 1600000000000000000),
            (exactRationalLiteral (-1278957353437049) 400000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-30452011668187151) 9600000000000000000),
            (exactRationalLiteral (5305567671706799) 800000000000000000),
            (exactRationalLiteral (69658877201201) 40000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (130738417240780631) 9600000000000000000),
            (exactRationalLiteral (-7803901010639857) 800000000000000000),
            (exactRationalLiteral (215778861398567) 200000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (418738037644792799) 9600000000000000000),
            (exactRationalLiteral (-22771995228915709) 800000000000000000),
            (exactRationalLiteral (2606902278471431) 200000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-190902261792577523) 6400000000000000000),
            (exactRationalLiteral (46687445982040427) 1600000000000000000),
            (exactRationalLiteral (-6572560857736737) 400000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-139590504331277661) 6400000000000000000),
            (exactRationalLiteral (12000214534953349) 1600000000000000000),
            (exactRationalLiteral (-2033114321103) 400000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8491818311551463) 1600000000000000000),
            (exactRationalLiteral (-310785276510109) 400000000000000000),
            (exactRationalLiteral (252053580947811) 100000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-190757555586803863) 1600000000000000000),
            (exactRationalLiteral (6114229926246439) 100000000000000000),
            (exactRationalLiteral (-409330354652571) 20000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2430765386427549413) 9600000000000000000),
            (exactRationalLiteral (-105768582512461179) 800000000000000000),
            (exactRationalLiteral (1669875796012513) 40000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-190757555586803863) 1600000000000000000),
            (exactRationalLiteral (6114229926246439) 100000000000000000),
            (exactRationalLiteral (-409330354652571) 20000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-8491818311551463) 1600000000000000000),
            (exactRationalLiteral (-310785276510109) 400000000000000000),
            (exactRationalLiteral (252053580947811) 100000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-139590504331277661) 6400000000000000000),
            (exactRationalLiteral (12000214534953349) 1600000000000000000),
            (exactRationalLiteral (-2033114321103) 400000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-190902261792577523) 6400000000000000000),
            (exactRationalLiteral (46687445982040427) 1600000000000000000),
            (exactRationalLiteral (-6572560857736737) 400000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (418738037644792799) 9600000000000000000),
            (exactRationalLiteral (-22771995228915709) 800000000000000000),
            (exactRationalLiteral (2606902278471431) 200000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (130738417240780631) 9600000000000000000),
            (exactRationalLiteral (-7803901010639857) 800000000000000000),
            (exactRationalLiteral (215778861398567) 200000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-30452011668187151) 9600000000000000000),
            (exactRationalLiteral (5305567671706799) 800000000000000000),
            (exactRationalLiteral (69658877201201) 40000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1621912189971497) 19200000000000000000),
            (exactRationalLiteral (-6356373718624481) 1600000000000000000),
            (exactRationalLiteral (-1278957353437049) 400000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (127114631967087491) 9600000000000000000),
            (exactRationalLiteral (11362921065498701) 800000000000000000),
            (exactRationalLiteral (1408436698376879) 200000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-71786423775515093) 6400000000000000000),
            (exactRationalLiteral (-15494789790956691) 1600000000000000000),
            (exactRationalLiteral (-603761233716363) 80000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-63783844457141047) 3200000000000000000),
            (exactRationalLiteral (-7367612654106651) 800000000000000000),
            (exactRationalLiteral (-435514155470841) 200000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4213225472049163) 600000000000000000),
            (exactRationalLiteral (2874826489633573) 400000000000000000),
            (exactRationalLiteral (167377408937287) 50000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (51187784528156153) 9600000000000000000),
            (exactRationalLiteral (-131312160593069) 800000000000000000),
            (exactRationalLiteral (123499793914517) 200000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (264127484437433) 128000000000000000),
            (exactRationalLiteral (5471437465867683) 800000000000000000),
            (exactRationalLiteral (-593389250081709) 200000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-8506360635618461) 800000000000000000),
            (exactRationalLiteral (-1559420003697729) 50000000000000000),
            (exactRationalLiteral (401092797459219) 50000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (150305125865855617) 6400000000000000000),
            (exactRationalLiteral (197025680480098211) 1600000000000000000),
            (exactRationalLiteral (12266461938451491) 400000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (222240998353277563) 6400000000000000000),
            (exactRationalLiteral (-58924750965017911) 320000000000000000),
            (exactRationalLiteral (-55372291719574407) 400000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-55214453694390111) 640000000000000000),
            (exactRationalLiteral (13602871079162807) 160000000000000000),
            (exactRationalLiteral (38720707219783623) 200000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (7839420388222457) 240000000000000000),
            (exactRationalLiteral (368847865928483) 16000000000000000),
            (exactRationalLiteral (-1185716067840809) 10000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 6400000000000000000),
            (exactRationalLiteral (-32695951386181797) 1600000000000000000),
            (exactRationalLiteral (10898650462060599) 400000000000000000),
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
          (exactRationalLiteral (2877660045060783) 80000000000000000),
          (exactRationalLiteral (29984629169230613) 300000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (129426747041636107) 2400000000000000000),
          (exactRationalLiteral (10197493976142871) 600000000000000000),
          (exactRationalLiteral (1331470937150337) 400000000000000000),
          (exactRationalLiteral (3247229452306183) 600000000000000000),
          (exactRationalLiteral (10810307381175853) 1200000000000000000),
          (exactRationalLiteral (1674210593348903) 75000000000000000),
          (exactRationalLiteral (34110043632426913) 2400000000000000000),
          (exactRationalLiteral (2588754847869827) 150000000000000000),
          (exactRationalLiteral (2849613051421861) 2400000000000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (13528988273551) 2500000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (21674719072611743) 75000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (13528988273551) 2500000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (2849613051421861) 2400000000000000000),
          (exactRationalLiteral (2588754847869827) 150000000000000000),
          (exactRationalLiteral (34110043632426913) 2400000000000000000),
          (exactRationalLiteral (1674210593348903) 75000000000000000),
          (exactRationalLiteral (10810307381175853) 1200000000000000000),
          (exactRationalLiteral (3247229452306183) 600000000000000000),
          (exactRationalLiteral (1331470937150337) 400000000000000000),
          (exactRationalLiteral (10197493976142871) 600000000000000000),
          (exactRationalLiteral (129426747041636107) 2400000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (29984629169230613) 300000000000000000),
          (exactRationalLiteral (2877660045060783) 80000000000000000),
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
      (45, 18),
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
      (44, 53)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 19200000000000000000),
            (exactRationalLiteral (-3632883487353533) 1600000000000000000),
            (exactRationalLiteral (3632883487353533) 400000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11148695861220311) 480000000000000000),
            (exactRationalLiteral (-3475759303146197) 80000000000000000),
            (exactRationalLiteral (-18035448794543) 1250000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-50644103158335441) 3200000000000000000),
            (exactRationalLiteral (24934424547845471) 160000000000000000),
            (exactRationalLiteral (-10391823548076963) 200000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1275681076585693357) 19200000000000000000),
            (exactRationalLiteral (-271209942733435099) 1600000000000000000),
            (exactRationalLiteral (13415839553080327) 80000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1433244375578557201) 19200000000000000000),
            (exactRationalLiteral (72580214153395771) 1600000000000000000),
            (exactRationalLiteral (-74489195101802711) 400000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-40221107191858331) 2400000000000000000),
            (exactRationalLiteral (6753377800253) 312500000000000),
            (exactRationalLiteral (4878828106017199) 50000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (8536762406191531) 3200000000000000000),
            (exactRationalLiteral (-6855733488688389) 800000000000000000),
            (exactRationalLiteral (-5570196227196327) 200000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (19320834609361909) 3200000000000000000),
            (exactRationalLiteral (3402984383321891) 800000000000000000),
            (exactRationalLiteral (1643648478042963) 200000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9037545855829161) 800000000000000000),
            (exactRationalLiteral (3840573064274537) 400000000000000000),
            (exactRationalLiteral (37029617361477) 25000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1896701730797959) 76800000000000000),
            (exactRationalLiteral (-7261837870005883) 800000000000000000),
            (exactRationalLiteral (19536061900849) 8000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-360396002929303261) 19200000000000000000),
            (exactRationalLiteral (-35491173882301979) 1600000000000000000),
            (exactRationalLiteral (-6979385877090829) 400000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (214206238780239821) 9600000000000000000),
            (exactRationalLiteral (3600617575765001) 160000000000000000),
            (exactRationalLiteral (1911646708286273) 200000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-41259634784713379) 19200000000000000000),
            (exactRationalLiteral (-4548199153247881) 1600000000000000000),
            (exactRationalLiteral (2183044636125349) 400000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-452683987242337) 9600000000000000000),
            (exactRationalLiteral (3691939725046799) 800000000000000000),
            (exactRationalLiteral (-231021671867201) 40000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (3517672547971589) 384000000000000000),
            (exactRationalLiteral (-6222057472262873) 800000000000000000),
            (exactRationalLiteral (23005716311597) 8000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2472803168721313) 76800000000000000),
            (exactRationalLiteral (-14488634876425781) 800000000000000000),
            (exactRationalLiteral (1534777897773533) 200000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-359816110109479627) 19200000000000000000),
            (exactRationalLiteral (26215567385519091) 1600000000000000000),
            (exactRationalLiteral (-3663378440523931) 400000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-348615663786700613) 19200000000000000000),
            (exactRationalLiteral (11081561762301693) 1600000000000000000),
            (exactRationalLiteral (-18291730880189) 16000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24816614077496423) 4800000000000000000),
            (exactRationalLiteral (446883819703579) 400000000000000000),
            (exactRationalLiteral (126780967159033) 100000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-89500386381133741) 960000000000000000),
            (exactRationalLiteral (439120789098141) 10000000000000000),
            (exactRationalLiteral (-1399392297267203) 100000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1886388276000073447) 9600000000000000000),
            (exactRationalLiteral (-15470029629788151) 160000000000000000),
            (exactRationalLiteral (5859838201697647) 200000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-89500386381133741) 960000000000000000),
            (exactRationalLiteral (439120789098141) 10000000000000000),
            (exactRationalLiteral (-1399392297267203) 100000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-24816614077496423) 4800000000000000000),
            (exactRationalLiteral (446883819703579) 400000000000000000),
            (exactRationalLiteral (126780967159033) 100000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-348615663786700613) 19200000000000000000),
            (exactRationalLiteral (11081561762301693) 1600000000000000000),
            (exactRationalLiteral (-18291730880189) 16000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-359816110109479627) 19200000000000000000),
            (exactRationalLiteral (26215567385519091) 1600000000000000000),
            (exactRationalLiteral (-3663378440523931) 400000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2472803168721313) 76800000000000000),
            (exactRationalLiteral (-14488634876425781) 800000000000000000),
            (exactRationalLiteral (1534777897773533) 200000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3517672547971589) 384000000000000000),
            (exactRationalLiteral (-6222057472262873) 800000000000000000),
            (exactRationalLiteral (23005716311597) 8000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-452683987242337) 9600000000000000000),
            (exactRationalLiteral (3691939725046799) 800000000000000000),
            (exactRationalLiteral (-231021671867201) 40000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-41259634784713379) 19200000000000000000),
            (exactRationalLiteral (-4548199153247881) 1600000000000000000),
            (exactRationalLiteral (2183044636125349) 400000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (214206238780239821) 9600000000000000000),
            (exactRationalLiteral (3600617575765001) 160000000000000000),
            (exactRationalLiteral (1911646708286273) 200000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-360396002929303261) 19200000000000000000),
            (exactRationalLiteral (-35491173882301979) 1600000000000000000),
            (exactRationalLiteral (-6979385877090829) 400000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1896701730797959) 76800000000000000),
            (exactRationalLiteral (-7261837870005883) 800000000000000000),
            (exactRationalLiteral (19536061900849) 8000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9037545855829161) 800000000000000000),
            (exactRationalLiteral (3840573064274537) 400000000000000000),
            (exactRationalLiteral (37029617361477) 25000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (19320834609361909) 3200000000000000000),
            (exactRationalLiteral (3402984383321891) 800000000000000000),
            (exactRationalLiteral (1643648478042963) 200000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8536762406191531) 3200000000000000000),
            (exactRationalLiteral (-6855733488688389) 800000000000000000),
            (exactRationalLiteral (-5570196227196327) 200000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-40221107191858331) 2400000000000000000),
            (exactRationalLiteral (6753377800253) 312500000000000),
            (exactRationalLiteral (4878828106017199) 50000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (1433244375578557201) 19200000000000000000),
            (exactRationalLiteral (72580214153395771) 1600000000000000000),
            (exactRationalLiteral (-74489195101802711) 400000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1275681076585693357) 19200000000000000000),
            (exactRationalLiteral (-271209942733435099) 1600000000000000000),
            (exactRationalLiteral (13415839553080327) 80000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-50644103158335441) 3200000000000000000),
            (exactRationalLiteral (24934424547845471) 160000000000000000),
            (exactRationalLiteral (-10391823548076963) 200000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (11148695861220311) 480000000000000000),
            (exactRationalLiteral (-3475759303146197) 80000000000000000),
            (exactRationalLiteral (-18035448794543) 1250000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 19200000000000000000),
            (exactRationalLiteral (-3632883487353533) 1600000000000000000),
            (exactRationalLiteral (3632883487353533) 400000000000000000),
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
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (50740362917308837) 600000000000000000),
          (exactRationalLiteral (786387157262641) 40000000000000000),
          (exactRationalLiteral (5924635574317) 1600000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (1553808736527119) 600000000000000000),
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
          (exactRationalLiteral (1553808736527119) 600000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (5924635574317) 1600000000000000),
          (exactRationalLiteral (786387157262641) 40000000000000000),
          (exactRationalLiteral (50740362917308837) 600000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
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
      (45, 19),
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
      (44, 52)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (1246079036162261819) 153600000000000000000),
            (exactRationalLiteral (-178011290880323117) 6400000000000000000),
            (exactRationalLiteral (25430184411474731) 800000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (71153518391945157) 2560000000000000000),
            (exactRationalLiteral (17904118338780597) 320000000000000000),
            (exactRationalLiteral (-5784296748847701) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-2395008733124649903) 25600000000000000000),
            (exactRationalLiteral (18523665464038271) 640000000000000000),
            (exactRationalLiteral (101997679823497539) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8475809523319801709) 153600000000000000000),
            (exactRationalLiteral (-895780107679572571) 6400000000000000000),
            (exactRationalLiteral (-34394065636327367) 160000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1359991455170192323) 153600000000000000000),
            (exactRationalLiteral (695659045646459779) 6400000000000000000),
            (exactRationalLiteral (67910752397030083) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32283201486718937) 4800000000000000000),
            (exactRationalLiteral (-486324471894431) 16000000000000000),
            (exactRationalLiteral (-179585257420069) 12500000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (30582436353371553) 25600000000000000000),
            (exactRationalLiteral (21770903375240259) 3200000000000000000),
            (exactRationalLiteral (1301624988393891) 400000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (411058946573788931) 76800000000000000000),
            (exactRationalLiteral (-259173475966121) 3200000000000000000),
            (exactRationalLiteral (-513074754235189) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (237250359417005333) 38400000000000000000),
            (exactRationalLiteral (10066968512821663) 1600000000000000000),
            (exactRationalLiteral (762827809963481) 200000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-289095191581285279) 15360000000000000000),
            (exactRationalLiteral (-27266436143047207) 3200000000000000000),
            (exactRationalLiteral (-266597232487543) 80000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1553069240278118323) 153600000000000000000),
            (exactRationalLiteral (-51884224343754011) 6400000000000000000),
            (exactRationalLiteral (-4057322482909123) 800000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (888761018136022093) 76800000000000000000),
            (exactRationalLiteral (8013908494688397) 640000000000000000),
            (exactRationalLiteral (2565268391799061) 400000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (53896441988318303) 153600000000000000000),
            (exactRationalLiteral (-18578664465968529) 6400000000000000000),
            (exactRationalLiteral (-4288915701655297) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-101480479239090587) 25600000000000000000),
            (exactRationalLiteral (19077391770132171) 3200000000000000000),
            (exactRationalLiteral (289658028936603) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (228133828239823811) 15360000000000000000),
            (exactRationalLiteral (-31899037464958017) 3200000000000000000),
            (exactRationalLiteral (50375139920291) 80000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (727869143953301687) 15360000000000000000),
            (exactRationalLiteral (-102051652219897509) 3200000000000000000),
            (exactRationalLiteral (5749866747291811) 400000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-5182793591161372501) 153600000000000000000),
            (exactRationalLiteral (214494618567715059) 6400000000000000000),
            (exactRationalLiteral (-14599712924079877) 800000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3493959246977188859) 153600000000000000000),
            (exactRationalLiteral (47781360518255997) 6400000000000000000),
            (exactRationalLiteral (44712770039921) 160000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-198499258366532549) 38400000000000000000),
            (exactRationalLiteral (-2313991736726069) 1600000000000000000),
            (exactRationalLiteral (566743468790011) 200000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-244213395546034837) 1920000000000000000),
            (exactRationalLiteral (10633791565099227) 160000000000000000),
            (exactRationalLiteral (-276058330282721) 12500000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (6922229041946495767) 25600000000000000000),
            (exactRationalLiteral (-91543323271855487) 640000000000000000),
            (exactRationalLiteral (17943528349307589) 400000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-244213395546034837) 1920000000000000000),
            (exactRationalLiteral (10633791565099227) 160000000000000000),
            (exactRationalLiteral (-276058330282721) 12500000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-198499258366532549) 38400000000000000000),
            (exactRationalLiteral (-2313991736726069) 1600000000000000000),
            (exactRationalLiteral (566743468790011) 200000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3493959246977188859) 153600000000000000000),
            (exactRationalLiteral (47781360518255997) 6400000000000000000),
            (exactRationalLiteral (44712770039921) 160000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5182793591161372501) 153600000000000000000),
            (exactRationalLiteral (214494618567715059) 6400000000000000000),
            (exactRationalLiteral (-14599712924079877) 800000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (727869143953301687) 15360000000000000000),
            (exactRationalLiteral (-102051652219897509) 3200000000000000000),
            (exactRationalLiteral (5749866747291811) 400000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (228133828239823811) 15360000000000000000),
            (exactRationalLiteral (-31899037464958017) 3200000000000000000),
            (exactRationalLiteral (50375139920291) 80000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-101480479239090587) 25600000000000000000),
            (exactRationalLiteral (19077391770132171) 3200000000000000000),
            (exactRationalLiteral (289658028936603) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (53896441988318303) 153600000000000000000),
            (exactRationalLiteral (-18578664465968529) 6400000000000000000),
            (exactRationalLiteral (-4288915701655297) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (888761018136022093) 76800000000000000000),
            (exactRationalLiteral (8013908494688397) 640000000000000000),
            (exactRationalLiteral (2565268391799061) 400000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1553069240278118323) 153600000000000000000),
            (exactRationalLiteral (-51884224343754011) 6400000000000000000),
            (exactRationalLiteral (-4057322482909123) 800000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-289095191581285279) 15360000000000000000),
            (exactRationalLiteral (-27266436143047207) 3200000000000000000),
            (exactRationalLiteral (-266597232487543) 80000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (237250359417005333) 38400000000000000000),
            (exactRationalLiteral (10066968512821663) 1600000000000000000),
            (exactRationalLiteral (762827809963481) 200000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (411058946573788931) 76800000000000000000),
            (exactRationalLiteral (-259173475966121) 3200000000000000000),
            (exactRationalLiteral (-513074754235189) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (30582436353371553) 25600000000000000000),
            (exactRationalLiteral (21770903375240259) 3200000000000000000),
            (exactRationalLiteral (1301624988393891) 400000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-32283201486718937) 4800000000000000000),
            (exactRationalLiteral (-486324471894431) 16000000000000000),
            (exactRationalLiteral (-179585257420069) 12500000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (1359991455170192323) 153600000000000000000),
            (exactRationalLiteral (695659045646459779) 6400000000000000000),
            (exactRationalLiteral (67910752397030083) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8475809523319801709) 153600000000000000000),
            (exactRationalLiteral (-895780107679572571) 6400000000000000000),
            (exactRationalLiteral (-34394065636327367) 160000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2395008733124649903) 25600000000000000000),
            (exactRationalLiteral (18523665464038271) 640000000000000000),
            (exactRationalLiteral (101997679823497539) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (71153518391945157) 2560000000000000000),
            (exactRationalLiteral (17904118338780597) 320000000000000000),
            (exactRationalLiteral (-5784296748847701) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (1246079036162261819) 153600000000000000000),
            (exactRationalLiteral (-178011290880323117) 6400000000000000000),
            (exactRationalLiteral (25430184411474731) 800000000000000000),
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
          (exactRationalLiteral (7839420388222457) 240000000000000000),
          (exactRationalLiteral (57845300561731007) 600000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (150305125865855617) 6400000000000000000),
          (exactRationalLiteral (8506360635618461) 800000000000000000),
          (exactRationalLiteral (264127484437433) 128000000000000000),
          (exactRationalLiteral (6446738580407101) 1200000000000000000),
          (exactRationalLiteral (4213225472049163) 600000000000000000),
          (exactRationalLiteral (63783844457141047) 3200000000000000000),
          (exactRationalLiteral (71786423775515093) 6400000000000000000),
          (exactRationalLiteral (127114631967087491) 9600000000000000000),
          (exactRationalLiteral (58004569877) 93750000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (8491818311551463) 1600000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (21674719072611743) 75000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (8491818311551463) 1600000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (58004569877) 93750000000000),
          (exactRationalLiteral (127114631967087491) 9600000000000000000),
          (exactRationalLiteral (71786423775515093) 6400000000000000000),
          (exactRationalLiteral (63783844457141047) 3200000000000000000),
          (exactRationalLiteral (4213225472049163) 600000000000000000),
          (exactRationalLiteral (6446738580407101) 1200000000000000000),
          (exactRationalLiteral (264127484437433) 128000000000000000),
          (exactRationalLiteral (8506360635618461) 800000000000000000),
          (exactRationalLiteral (150305125865855617) 6400000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (57845300561731007) 600000000000000000),
          (exactRationalLiteral (7839420388222457) 240000000000000000),
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
      (43, 10),
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
      (42, 17)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 1228800000000000000),
            (exactRationalLiteral (-3632883487353533) 256000000000000000),
            (exactRationalLiteral (3632883487353533) 160000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (259805164042222361) 7680000000000000000),
            (exactRationalLiteral (-1067338746672347) 320000000000000000),
            (exactRationalLiteral (-3701431793878771) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-373452946709484897) 5120000000000000000),
            (exactRationalLiteral (402383985078460339) 3200000000000000000),
            (exactRationalLiteral (52885149055636953) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1527290897002628431) 153600000000000000000),
            (exactRationalLiteral (-1338758441436167827) 6400000000000000000),
            (exactRationalLiteral (-49518838696660793) 800000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1200370425930459037) 30720000000000000000),
            (exactRationalLiteral (793790741154071707) 6400000000000000000),
            (exactRationalLiteral (-18844904643224119) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-34294923874162469) 2400000000000000000),
            (exactRationalLiteral (-10553740607523899) 400000000000000000),
            (exactRationalLiteral (760263312299357) 25000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (72695000421274811) 25600000000000000000),
            (exactRationalLiteral (17023789374586587) 3200000000000000000),
            (exactRationalLiteral (-3675181988720727) 400000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (136475867801227907) 25600000000000000000),
            (exactRationalLiteral (145764975070003) 640000000000000000),
            (exactRationalLiteral (1007073929893257) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (102019852939927473) 12800000000000000000),
            (exactRationalLiteral (2549001411163651) 320000000000000000),
            (exactRationalLiteral (115238292306963) 40000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1621374745901993953) 76800000000000000000),
            (exactRationalLiteral (-6150109877362787) 640000000000000000),
            (exactRationalLiteral (-409070459445649) 400000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1928904774969587921) 153600000000000000000),
            (exactRationalLiteral (-76034673692408531) 6400000000000000000),
            (exactRationalLiteral (-8017902191418137) 800000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1161974333717900311) 76800000000000000000),
            (exactRationalLiteral (51337036060457017) 3200000000000000000),
            (exactRationalLiteral (613695680341691) 80000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-95194525269106843) 153600000000000000000),
            (exactRationalLiteral (-28810323293464921) 6400000000000000000),
            (exactRationalLiteral (-826913712092899) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-35722243268330119) 15360000000000000000),
            (exactRationalLiteral (21863746858180211) 3200000000000000000),
            (exactRationalLiteral (-11022520131799) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (190746976198030769) 15360000000000000000),
            (exactRationalLiteral (-30172806573769481) 3200000000000000000),
            (exactRationalLiteral (611239745992813) 400000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3091745709891833521) 76800000000000000000),
            (exactRationalLiteral (-81196433992126061) 3200000000000000000),
            (exactRationalLiteral (4677742366593913) 400000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-4059385705175189447) 153600000000000000000),
            (exactRationalLiteral (161914131705821163) 6400000000000000000),
            (exactRationalLiteral (-11690530506867071) 800000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-641281871659198421) 30720000000000000000),
            (exactRationalLiteral (47765095603687173) 6400000000000000000),
            (exactRationalLiteral (-231696307484017) 800000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-206083377616563943) 38400000000000000000),
            (exactRationalLiteral (-297563089143581) 1600000000000000000),
            (exactRationalLiteral (441470855001233) 200000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-16783806947363449) 150000000000000000),
            (exactRationalLiteral (8996470146488943) 160000000000000000),
            (exactRationalLiteral (-942418452131971) 50000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (18225751604762054087) 76800000000000000000),
            (exactRationalLiteral (-78184316903755383) 640000000000000000),
            (exactRationalLiteral (15453987570942671) 400000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-16783806947363449) 150000000000000000),
            (exactRationalLiteral (8996470146488943) 160000000000000000),
            (exactRationalLiteral (-942418452131971) 50000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-206083377616563943) 38400000000000000000),
            (exactRationalLiteral (-297563089143581) 1600000000000000000),
            (exactRationalLiteral (441470855001233) 200000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-641281871659198421) 30720000000000000000),
            (exactRationalLiteral (47765095603687173) 6400000000000000000),
            (exactRationalLiteral (-231696307484017) 800000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4059385705175189447) 153600000000000000000),
            (exactRationalLiteral (161914131705821163) 6400000000000000000),
            (exactRationalLiteral (-11690530506867071) 800000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3091745709891833521) 76800000000000000000),
            (exactRationalLiteral (-81196433992126061) 3200000000000000000),
            (exactRationalLiteral (4677742366593913) 400000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (190746976198030769) 15360000000000000000),
            (exactRationalLiteral (-30172806573769481) 3200000000000000000),
            (exactRationalLiteral (611239745992813) 400000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-35722243268330119) 15360000000000000000),
            (exactRationalLiteral (21863746858180211) 3200000000000000000),
            (exactRationalLiteral (-11022520131799) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-95194525269106843) 153600000000000000000),
            (exactRationalLiteral (-28810323293464921) 6400000000000000000),
            (exactRationalLiteral (-826913712092899) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1161974333717900311) 76800000000000000000),
            (exactRationalLiteral (51337036060457017) 3200000000000000000),
            (exactRationalLiteral (613695680341691) 80000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1928904774969587921) 153600000000000000000),
            (exactRationalLiteral (-76034673692408531) 6400000000000000000),
            (exactRationalLiteral (-8017902191418137) 800000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1621374745901993953) 76800000000000000000),
            (exactRationalLiteral (-6150109877362787) 640000000000000000),
            (exactRationalLiteral (-409070459445649) 400000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (102019852939927473) 12800000000000000000),
            (exactRationalLiteral (2549001411163651) 320000000000000000),
            (exactRationalLiteral (115238292306963) 40000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (136475867801227907) 25600000000000000000),
            (exactRationalLiteral (145764975070003) 640000000000000000),
            (exactRationalLiteral (1007073929893257) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (72695000421274811) 25600000000000000000),
            (exactRationalLiteral (17023789374586587) 3200000000000000000),
            (exactRationalLiteral (-3675181988720727) 400000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-34294923874162469) 2400000000000000000),
            (exactRationalLiteral (-10553740607523899) 400000000000000000),
            (exactRationalLiteral (760263312299357) 25000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (1200370425930459037) 30720000000000000000),
            (exactRationalLiteral (793790741154071707) 6400000000000000000),
            (exactRationalLiteral (-18844904643224119) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1527290897002628431) 153600000000000000000),
            (exactRationalLiteral (-1338758441436167827) 6400000000000000000),
            (exactRationalLiteral (-49518838696660793) 800000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-373452946709484897) 5120000000000000000),
            (exactRationalLiteral (402383985078460339) 3200000000000000000),
            (exactRationalLiteral (52885149055636953) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (259805164042222361) 7680000000000000000),
            (exactRationalLiteral (-1067338746672347) 320000000000000000),
            (exactRationalLiteral (-3701431793878771) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 1228800000000000000),
            (exactRationalLiteral (-3632883487353533) 256000000000000000),
            (exactRationalLiteral (3632883487353533) 160000000000000000),
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
          (exactRationalLiteral (11067306960844081) 320000000000000000),
          (exactRationalLiteral (55214453694390111) 640000000000000000),
          (exactRationalLiteral (222240998353277563) 6400000000000000000),
          (exactRationalLiteral (129426747041636107) 2400000000000000000),
          (exactRationalLiteral (10197493976142871) 600000000000000000),
          (exactRationalLiteral (1331470937150337) 400000000000000000),
          (exactRationalLiteral (649055272127309) 120000000000000000),
          (exactRationalLiteral (10810307381175853) 1200000000000000000),
          (exactRationalLiteral (1674210593348903) 75000000000000000),
          (exactRationalLiteral (34110043632426913) 2400000000000000000),
          (exactRationalLiteral (2588754847869827) 150000000000000000),
          (exactRationalLiteral (2849613051421861) 2400000000000000000),
          (exactRationalLiteral (30452011668187151) 9600000000000000000),
          (exactRationalLiteral (130738417240780631) 9600000000000000000),
          (exactRationalLiteral (418738037644792799) 9600000000000000000),
          (exactRationalLiteral (190902261792577523) 6400000000000000000),
          (exactRationalLiteral (139590504331277661) 6400000000000000000),
          (exactRationalLiteral (6461242976681699) 1200000000000000000),
          (exactRationalLiteral (190757555586803863) 1600000000000000000),
          (exactRationalLiteral (2430765386427549413) 9600000000000000000),
          (exactRationalLiteral (190757555586803863) 1600000000000000000),
          (exactRationalLiteral (6461242976681699) 1200000000000000000),
          (exactRationalLiteral (139590504331277661) 6400000000000000000),
          (exactRationalLiteral (190902261792577523) 6400000000000000000),
          (exactRationalLiteral (418738037644792799) 9600000000000000000),
          (exactRationalLiteral (130738417240780631) 9600000000000000000),
          (exactRationalLiteral (30452011668187151) 9600000000000000000),
          (exactRationalLiteral (2849613051421861) 2400000000000000000),
          (exactRationalLiteral (2588754847869827) 150000000000000000),
          (exactRationalLiteral (34110043632426913) 2400000000000000000),
          (exactRationalLiteral (1674210593348903) 75000000000000000),
          (exactRationalLiteral (10810307381175853) 1200000000000000000),
          (exactRationalLiteral (649055272127309) 120000000000000000),
          (exactRationalLiteral (1331470937150337) 400000000000000000),
          (exactRationalLiteral (10197493976142871) 600000000000000000),
          (exactRationalLiteral (129426747041636107) 2400000000000000000),
          (exactRationalLiteral (222240998353277563) 6400000000000000000),
          (exactRationalLiteral (55214453694390111) 640000000000000000),
          (exactRationalLiteral (11067306960844081) 320000000000000000),
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
      (43, 11),
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
      (42, 16)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 51200000000000000000),
            (exactRationalLiteral (-32695951386181797) 6400000000000000000),
            (exactRationalLiteral (10898650462060599) 800000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (217315409855518747) 7680000000000000000),
            (exactRationalLiteral (-11707336012249571) 320000000000000000),
            (exactRationalLiteral (-1618566838909841) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-916439541525103443) 25600000000000000000),
            (exactRationalLiteral (515699519765286979) 3200000000000000000),
            (exactRationalLiteral (3772618287776367) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2203226619344801293) 51200000000000000000),
            (exactRationalLiteral (-258386163450571783) 1280000000000000000),
            (exactRationalLiteral (72932650788315249) 800000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3397145030899006397) 51200000000000000000),
            (exactRationalLiteral (544899808500666827) 6400000000000000000),
            (exactRationalLiteral (-105600561683478321) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-28883391504915457) 1600000000000000000),
            (exactRationalLiteral (6101199428937) 400000000000000000),
            (exactRationalLiteral (469924284859713) 6250000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (85406108579412253) 25600000000000000000),
            (exactRationalLiteral (-7630552534525557) 3200000000000000000),
            (exactRationalLiteral (-1730397793167069) 80000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (431966034551016679) 76800000000000000000),
            (exactRationalLiteral (1559483592635987) 640000000000000000),
            (exactRationalLiteral (2527222614021703) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (77739470659879013) 7680000000000000000),
            (exactRationalLiteral (14676500205100183) 1600000000000000000),
            (exactRationalLiteral (389555113106149) 200000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-602363741641419029) 25600000000000000000),
            (exactRationalLiteral (-30538999818612399) 3200000000000000000),
            (exactRationalLiteral (514845243546417) 400000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-832389987418364269) 51200000000000000000),
            (exactRationalLiteral (-116027441875099107) 6400000000000000000),
            (exactRationalLiteral (-11978481899927151) 800000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1508831130940781449) 76800000000000000000),
            (exactRationalLiteral (516938957496877) 25600000000000000),
            (exactRationalLiteral (3571688411617849) 400000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-52826284323352313) 30720000000000000000),
            (exactRationalLiteral (-25193974162711721) 6400000000000000000),
            (exactRationalLiteral (2635088277469499) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-54103697381845309) 76800000000000000000),
            (exactRationalLiteral (18636490964860211) 3200000000000000000),
            (exactRationalLiteral (-311703069200201) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (781470374685016147) 76800000000000000000),
            (exactRationalLiteral (-27009119497015513) 3200000000000000000),
            (exactRationalLiteral (970603792384171) 400000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2656411516815412519) 76800000000000000000),
            (exactRationalLiteral (-12925942657429241) 640000000000000000),
            (exactRationalLiteral (721123597179203) 80000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1072183517117938699) 51200000000000000000),
            (exactRationalLiteral (120970374512778491) 6400000000000000000),
            (exactRationalLiteral (-1756269617930853) 160000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-974806726998137253) 51200000000000000000),
            (exactRationalLiteral (45927790058383861) 6400000000000000000),
            (exactRationalLiteral (-686956465167639) 800000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13538146423104383) 2560000000000000000),
            (exactRationalLiteral (243555020656759) 320000000000000000),
            (exactRationalLiteral (63239648242491) 40000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-316626118127838197) 3200000000000000000),
            (exactRationalLiteral (38090262591384599) 800000000000000000),
            (exactRationalLiteral (-390301791566529) 25000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (16055711785387244977) 76800000000000000000),
            (exactRationalLiteral (-334084715791736067) 3200000000000000000),
            (exactRationalLiteral (12964446792577753) 400000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-316626118127838197) 3200000000000000000),
            (exactRationalLiteral (38090262591384599) 800000000000000000),
            (exactRationalLiteral (-390301791566529) 25000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-13538146423104383) 2560000000000000000),
            (exactRationalLiteral (243555020656759) 320000000000000000),
            (exactRationalLiteral (63239648242491) 40000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-974806726998137253) 51200000000000000000),
            (exactRationalLiteral (45927790058383861) 6400000000000000000),
            (exactRationalLiteral (-686956465167639) 800000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1072183517117938699) 51200000000000000000),
            (exactRationalLiteral (120970374512778491) 6400000000000000000),
            (exactRationalLiteral (-1756269617930853) 160000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2656411516815412519) 76800000000000000000),
            (exactRationalLiteral (-12925942657429241) 640000000000000000),
            (exactRationalLiteral (721123597179203) 80000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (781470374685016147) 76800000000000000000),
            (exactRationalLiteral (-27009119497015513) 3200000000000000000),
            (exactRationalLiteral (970603792384171) 400000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-54103697381845309) 76800000000000000000),
            (exactRationalLiteral (18636490964860211) 3200000000000000000),
            (exactRationalLiteral (-311703069200201) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-52826284323352313) 30720000000000000000),
            (exactRationalLiteral (-25193974162711721) 6400000000000000000),
            (exactRationalLiteral (2635088277469499) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1508831130940781449) 76800000000000000000),
            (exactRationalLiteral (516938957496877) 25600000000000000),
            (exactRationalLiteral (3571688411617849) 400000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-832389987418364269) 51200000000000000000),
            (exactRationalLiteral (-116027441875099107) 6400000000000000000),
            (exactRationalLiteral (-11978481899927151) 800000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-602363741641419029) 25600000000000000000),
            (exactRationalLiteral (-30538999818612399) 3200000000000000000),
            (exactRationalLiteral (514845243546417) 400000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (77739470659879013) 7680000000000000000),
            (exactRationalLiteral (14676500205100183) 1600000000000000000),
            (exactRationalLiteral (389555113106149) 200000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (431966034551016679) 76800000000000000000),
            (exactRationalLiteral (1559483592635987) 640000000000000000),
            (exactRationalLiteral (2527222614021703) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (85406108579412253) 25600000000000000000),
            (exactRationalLiteral (-7630552534525557) 3200000000000000000),
            (exactRationalLiteral (-1730397793167069) 80000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-28883391504915457) 1600000000000000000),
            (exactRationalLiteral (6101199428937) 400000000000000000),
            (exactRationalLiteral (469924284859713) 6250000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (3397145030899006397) 51200000000000000000),
            (exactRationalLiteral (544899808500666827) 6400000000000000000),
            (exactRationalLiteral (-105600561683478321) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2203226619344801293) 51200000000000000000),
            (exactRationalLiteral (-258386163450571783) 1280000000000000000),
            (exactRationalLiteral (72932650788315249) 800000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-916439541525103443) 25600000000000000000),
            (exactRationalLiteral (515699519765286979) 3200000000000000000),
            (exactRationalLiteral (3772618287776367) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (217315409855518747) 7680000000000000000),
            (exactRationalLiteral (-11707336012249571) 320000000000000000),
            (exactRationalLiteral (-1618566838909841) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 51200000000000000000),
            (exactRationalLiteral (-32695951386181797) 6400000000000000000),
            (exactRationalLiteral (10898650462060599) 800000000000000000),
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
          (exactRationalLiteral (1275681076585693357) 19200000000000000000),
          (exactRationalLiteral (1433244375578557201) 19200000000000000000),
          (exactRationalLiteral (44543268984020251) 2400000000000000000),
          (exactRationalLiteral (2812629830729587) 800000000000000000),
          (exactRationalLiteral (19320834609361909) 3200000000000000000),
          (exactRationalLiteral (9037545855829161) 800000000000000000),
          (exactRationalLiteral (1896701730797959) 76800000000000000),
          (exactRationalLiteral (360396002929303261) 19200000000000000000),
          (exactRationalLiteral (214206238780239821) 9600000000000000000),
          (exactRationalLiteral (41259634784713379) 19200000000000000000),
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
          (exactRationalLiteral (41259634784713379) 19200000000000000000),
          (exactRationalLiteral (214206238780239821) 9600000000000000000),
          (exactRationalLiteral (360396002929303261) 19200000000000000000),
          (exactRationalLiteral (1896701730797959) 76800000000000000),
          (exactRationalLiteral (9037545855829161) 800000000000000000),
          (exactRationalLiteral (19320834609361909) 3200000000000000000),
          (exactRationalLiteral (2812629830729587) 800000000000000000),
          (exactRationalLiteral (44543268984020251) 2400000000000000000),
          (exactRationalLiteral (1433244375578557201) 19200000000000000000),
          (exactRationalLiteral (1275681076585693357) 19200000000000000000),
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
      (43, 12),
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
      (42, 15)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 153600000000000000000),
            (exactRationalLiteral (-3632883487353533) 6400000000000000000),
            (exactRationalLiteral (3632883487353533) 800000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (45326683844992983) 2560000000000000000),
            (exactRationalLiteral (-560634938318043) 12800000000000000),
            (exactRationalLiteral (464298116059089) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (12913319359885707) 5120000000000000000),
            (exactRationalLiteral (17302597255226851) 128000000000000000),
            (exactRationalLiteral (-45339912480084219) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-12996266994151870213) 153600000000000000000),
            (exactRationalLiteral (-151059447025929167) 1280000000000000000),
            (exactRationalLiteral (195384140273291291) 800000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11846604575338263493) 153600000000000000000),
            (exactRationalLiteral (-51013752313754861) 6400000000000000000),
            (exactRationalLiteral (-192356218723732523) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14899442483658839) 1200000000000000000),
            (exactRationalLiteral (19521413623497733) 400000000000000000),
            (exactRationalLiteral (2999130966578347) 25000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (5780261002173387) 5120000000000000000),
            (exactRationalLiteral (-52192122352096173) 3200000000000000000),
            (exactRationalLiteral (-13628795942949963) 400000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (515157808434870509) 76800000000000000000),
            (exactRationalLiteral (20946605787523639) 3200000000000000000),
            (exactRationalLiteral (4047371298150149) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (480684470493555287) 38400000000000000000),
            (exactRationalLiteral (15861447960667447) 1600000000000000000),
            (exactRationalLiteral (202918764677483) 200000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1980451418101406213) 76800000000000000000),
            (exactRationalLiteral (-26631787438442599) 3200000000000000000),
            (exactRationalLiteral (1438760946538483) 400000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3352918715138849317) 153600000000000000000),
            (exactRationalLiteral (-171862528891825739) 6400000000000000000),
            (exactRationalLiteral (-3187812321687233) 160000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1941408450042490963) 76800000000000000000),
            (exactRationalLiteral (79910543353399809) 3200000000000000000),
            (exactRationalLiteral (4074898421527243) 400000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-369826199305148311) 153600000000000000000),
            (exactRationalLiteral (-7729617073708929) 6400000000000000000),
            (exactRationalLiteral (6097090267031897) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (10999817757978619) 25600000000000000000),
            (exactRationalLiteral (9395624090172171) 3200000000000000000),
            (exactRationalLiteral (-612383618268603) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (632500359397098553) 76800000000000000000),
            (exactRationalLiteral (-22407976234696113) 3200000000000000000),
            (exactRationalLiteral (1329967838775529) 400000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2307612155400495877) 76800000000000000000),
            (exactRationalLiteral (-52351490104957941) 3200000000000000000),
            (exactRationalLiteral (2533493605198117) 400000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2584467751684145107) 153600000000000000000),
            (exactRationalLiteral (91663346988587043) 6400000000000000000),
            (exactRationalLiteral (-5872165672441459) 800000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2658917958856854749) 153600000000000000000),
            (exactRationalLiteral (42269443882346061) 6400000000000000000),
            (exactRationalLiteral (-1142216622851261) 800000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-192472257287468627) 38400000000000000000),
            (exactRationalLiteral (2232022840556059) 1600000000000000000),
            (exactRationalLiteral (190925627423677) 200000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-422163775065480919) 4800000000000000000),
            (exactRationalLiteral (32492693402315787) 800000000000000000),
            (exactRationalLiteral (-123757742826829) 10000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (4732272896344767313) 25600000000000000000),
            (exactRationalLiteral (-287206010178154891) 3200000000000000000),
            (exactRationalLiteral (2094981202842567) 80000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-422163775065480919) 4800000000000000000),
            (exactRationalLiteral (32492693402315787) 800000000000000000),
            (exactRationalLiteral (-123757742826829) 10000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-192472257287468627) 38400000000000000000),
            (exactRationalLiteral (2232022840556059) 1600000000000000000),
            (exactRationalLiteral (190925627423677) 200000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2658917958856854749) 153600000000000000000),
            (exactRationalLiteral (42269443882346061) 6400000000000000000),
            (exactRationalLiteral (-1142216622851261) 800000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2584467751684145107) 153600000000000000000),
            (exactRationalLiteral (91663346988587043) 6400000000000000000),
            (exactRationalLiteral (-5872165672441459) 800000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2307612155400495877) 76800000000000000000),
            (exactRationalLiteral (-52351490104957941) 3200000000000000000),
            (exactRationalLiteral (2533493605198117) 400000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (632500359397098553) 76800000000000000000),
            (exactRationalLiteral (-22407976234696113) 3200000000000000000),
            (exactRationalLiteral (1329967838775529) 400000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10999817757978619) 25600000000000000000),
            (exactRationalLiteral (9395624090172171) 3200000000000000000),
            (exactRationalLiteral (-612383618268603) 80000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-369826199305148311) 153600000000000000000),
            (exactRationalLiteral (-7729617073708929) 6400000000000000000),
            (exactRationalLiteral (6097090267031897) 800000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1941408450042490963) 76800000000000000000),
            (exactRationalLiteral (79910543353399809) 3200000000000000000),
            (exactRationalLiteral (4074898421527243) 400000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3352918715138849317) 153600000000000000000),
            (exactRationalLiteral (-171862528891825739) 6400000000000000000),
            (exactRationalLiteral (-3187812321687233) 160000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1980451418101406213) 76800000000000000000),
            (exactRationalLiteral (-26631787438442599) 3200000000000000000),
            (exactRationalLiteral (1438760946538483) 400000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (480684470493555287) 38400000000000000000),
            (exactRationalLiteral (15861447960667447) 1600000000000000000),
            (exactRationalLiteral (202918764677483) 200000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (515157808434870509) 76800000000000000000),
            (exactRationalLiteral (20946605787523639) 3200000000000000000),
            (exactRationalLiteral (4047371298150149) 400000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5780261002173387) 5120000000000000000),
            (exactRationalLiteral (-52192122352096173) 3200000000000000000),
            (exactRationalLiteral (-13628795942949963) 400000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14899442483658839) 1200000000000000000),
            (exactRationalLiteral (19521413623497733) 400000000000000000),
            (exactRationalLiteral (2999130966578347) 25000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (11846604575338263493) 153600000000000000000),
            (exactRationalLiteral (-51013752313754861) 6400000000000000000),
            (exactRationalLiteral (-192356218723732523) 800000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12996266994151870213) 153600000000000000000),
            (exactRationalLiteral (-151059447025929167) 1280000000000000000),
            (exactRationalLiteral (195384140273291291) 800000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12913319359885707) 5120000000000000000),
            (exactRationalLiteral (17302597255226851) 128000000000000000),
            (exactRationalLiteral (-45339912480084219) 400000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (45326683844992983) 2560000000000000000),
            (exactRationalLiteral (-560634938318043) 12800000000000000),
            (exactRationalLiteral (464298116059089) 40000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 153600000000000000000),
            (exactRationalLiteral (-3632883487353533) 6400000000000000000),
            (exactRationalLiteral (3632883487353533) 800000000000000000),
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
          (exactRationalLiteral (86641834747143) 5000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (376456147432988243) 4800000000000000000),
          (exactRationalLiteral (40221107191858331) 2400000000000000000),
          (exactRationalLiteral (8536762406191531) 3200000000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (1003603926147579) 400000000000000000),
          (exactRationalLiteral (40038179607619) 60000000000000000),
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
          (exactRationalLiteral (40038179607619) 60000000000000000),
          (exactRationalLiteral (1003603926147579) 400000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (8536762406191531) 3200000000000000000),
          (exactRationalLiteral (40221107191858331) 2400000000000000000),
          (exactRationalLiteral (376456147432988243) 4800000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (86641834747143) 5000000000000000),
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
      (43, 13),
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
      (42, 14)
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
            (exactRationalLiteral (32695951386181797) 3276800000000000000),
            (exactRationalLiteral (-32695951386181797) 1024000000000000000),
            (exactRationalLiteral (10898650462060599) 320000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1457087808370745933) 61440000000000000000),
            (exactRationalLiteral (95795092827997657) 1280000000000000000),
            (exactRationalLiteral (-12610025975179867) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-3863672478567265227) 40960000000000000000),
            (exactRationalLiteral (-62073675397155029) 12800000000000000000),
            (exactRationalLiteral (228551625030925371) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (25820929921626991831) 409600000000000000000),
            (exactRationalLiteral (-2834013373249254923) 25600000000000000000),
            (exactRationalLiteral (-405166401105761691) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (198857695767088589) 81920000000000000000),
            (exactRationalLiteral (2467615344477591683) 25600000000000000000),
            (exactRationalLiteral (179199333314187267) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-125354454074798281) 25600000000000000000),
            (exactRationalLiteral (-44639649243582501) 1600000000000000000),
            (exactRationalLiteral (-2556115886500047) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (161008595132318273) 204800000000000000000),
            (exactRationalLiteral (79388710058828163) 12800000000000000000),
            (exactRationalLiteral (5091653465345091) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3287743131434429543) 614400000000000000000),
            (exactRationalLiteral (355135891028099) 2560000000000000000),
            (exactRationalLiteral (-1786223850534601) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1781869538216177927) 307200000000000000000),
            (exactRationalLiteral (7424648927443679) 1280000000000000000),
            (exactRationalLiteral (323794758828259) 80000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3748356768120322333) 204800000000000000000),
            (exactRationalLiteral (-20654368414188387) 2560000000000000000),
            (exactRationalLiteral (-3127930176371463) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3941435625047699561) 409600000000000000000),
            (exactRationalLiteral (-193287897297634059) 25600000000000000000),
            (exactRationalLiteral (-6134355111563739) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6644393640752712593) 614400000000000000000),
            (exactRationalLiteral (150268701331526393) 12800000000000000000),
            (exactRationalLiteral (195157271145737) 32000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (626651014293455791) 1228800000000000000000),
            (exactRationalLiteral (-55427994062471729) 25600000000000000000),
            (exactRationalLiteral (-10308832398091793) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-531003752147798209) 122880000000000000000),
            (exactRationalLiteral (69764705129125619) 12800000000000000000),
            (exactRationalLiteral (729656332407407) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1901894630269372339) 122880000000000000000),
            (exactRationalLiteral (-128423970635042209) 12800000000000000000),
            (exactRationalLiteral (324069376007231) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (30374420847444937403) 614400000000000000000),
            (exactRationalLiteral (-431742138059106229) 12800000000000000000),
            (exactRationalLiteral (12035795684932571) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14708445673618882127) 409600000000000000000),
            (exactRationalLiteral (917831917175786147) 25600000000000000000),
            (exactRationalLiteral (-30654017056766157) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1901565419257102893) 81920000000000000000),
            (exactRationalLiteral (190003556593383757) 25600000000000000000),
            (exactRationalLiteral (674757779241021) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-518921022990637703) 102400000000000000000),
            (exactRationalLiteral (-11585577128958709) 6400000000000000000),
            (exactRationalLiteral (1196123244474411) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6729503917437103367) 51200000000000000000),
            (exactRationalLiteral (8866860509601221) 128000000000000000),
            (exactRationalLiteral (-4578748153522449) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (171735002343512255621) 614400000000000000000),
            (exactRationalLiteral (-380777069844704511) 2560000000000000000),
            (exactRationalLiteral (37131827087797637) 800000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6729503917437103367) 51200000000000000000),
            (exactRationalLiteral (8866860509601221) 128000000000000000),
            (exactRationalLiteral (-4578748153522449) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-518921022990637703) 102400000000000000000),
            (exactRationalLiteral (-11585577128958709) 6400000000000000000),
            (exactRationalLiteral (1196123244474411) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1901565419257102893) 81920000000000000000),
            (exactRationalLiteral (190003556593383757) 25600000000000000000),
            (exactRationalLiteral (674757779241021) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14708445673618882127) 409600000000000000000),
            (exactRationalLiteral (917831917175786147) 25600000000000000000),
            (exactRationalLiteral (-30654017056766157) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (30374420847444937403) 614400000000000000000),
            (exactRationalLiteral (-431742138059106229) 12800000000000000000),
            (exactRationalLiteral (12035795684932571) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1901894630269372339) 122880000000000000000),
            (exactRationalLiteral (-128423970635042209) 12800000000000000000),
            (exactRationalLiteral (324069376007231) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-531003752147798209) 122880000000000000000),
            (exactRationalLiteral (69764705129125619) 12800000000000000000),
            (exactRationalLiteral (729656332407407) 160000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (626651014293455791) 1228800000000000000000),
            (exactRationalLiteral (-55427994062471729) 25600000000000000000),
            (exactRationalLiteral (-10308832398091793) 1600000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (6644393640752712593) 614400000000000000000),
            (exactRationalLiteral (150268701331526393) 12800000000000000000),
            (exactRationalLiteral (195157271145737) 32000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3941435625047699561) 409600000000000000000),
            (exactRationalLiteral (-193287897297634059) 25600000000000000000),
            (exactRationalLiteral (-6134355111563739) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3748356768120322333) 204800000000000000000),
            (exactRationalLiteral (-20654368414188387) 2560000000000000000),
            (exactRationalLiteral (-3127930176371463) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1781869538216177927) 307200000000000000000),
            (exactRationalLiteral (7424648927443679) 1280000000000000000),
            (exactRationalLiteral (323794758828259) 80000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3287743131434429543) 614400000000000000000),
            (exactRationalLiteral (355135891028099) 2560000000000000000),
            (exactRationalLiteral (-1786223850534601) 800000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (161008595132318273) 204800000000000000000),
            (exactRationalLiteral (79388710058828163) 12800000000000000000),
            (exactRationalLiteral (5091653465345091) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-125354454074798281) 25600000000000000000),
            (exactRationalLiteral (-44639649243582501) 1600000000000000000),
            (exactRationalLiteral (-2556115886500047) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (198857695767088589) 81920000000000000000),
            (exactRationalLiteral (2467615344477591683) 25600000000000000000),
            (exactRationalLiteral (179199333314187267) 1600000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (25820929921626991831) 409600000000000000000),
            (exactRationalLiteral (-2834013373249254923) 25600000000000000000),
            (exactRationalLiteral (-405166401105761691) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3863672478567265227) 40960000000000000000),
            (exactRationalLiteral (-62073675397155029) 12800000000000000000),
            (exactRationalLiteral (228551625030925371) 800000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1457087808370745933) 61440000000000000000),
            (exactRationalLiteral (95795092827997657) 1280000000000000000),
            (exactRationalLiteral (-12610025975179867) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 3276800000000000000),
            (exactRationalLiteral (-32695951386181797) 1024000000000000000),
            (exactRationalLiteral (10898650462060599) 320000000000000000),
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
          (exactRationalLiteral (71153518391945157) 2560000000000000000),
          (exactRationalLiteral (909705565836767633) 9600000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (1359991455170192323) 153600000000000000000),
          (exactRationalLiteral (32283201486718937) 4800000000000000000),
          (exactRationalLiteral (30582436353371553) 25600000000000000000),
          (exactRationalLiteral (102829530012438763) 19200000000000000000),
          (exactRationalLiteral (237250359417005333) 38400000000000000000),
          (exactRationalLiteral (289095191581285279) 15360000000000000000),
          (exactRationalLiteral (1553069240278118323) 153600000000000000000),
          (exactRationalLiteral (888761018136022093) 76800000000000000000),
          (exactRationalLiteral (58004569877) 93750000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (198499258366532549) 38400000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (21674719072611743) 75000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (198499258366532549) 38400000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (58004569877) 93750000000000),
          (exactRationalLiteral (888761018136022093) 76800000000000000000),
          (exactRationalLiteral (1553069240278118323) 153600000000000000000),
          (exactRationalLiteral (289095191581285279) 15360000000000000000),
          (exactRationalLiteral (237250359417005333) 38400000000000000000),
          (exactRationalLiteral (102829530012438763) 19200000000000000000),
          (exactRationalLiteral (30582436353371553) 25600000000000000000),
          (exactRationalLiteral (32283201486718937) 4800000000000000000),
          (exactRationalLiteral (1359991455170192323) 153600000000000000000),
          (exactRationalLiteral (20675806869279533) 300000000000000000),
          (exactRationalLiteral (909705565836767633) 9600000000000000000),
          (exactRationalLiteral (71153518391945157) 2560000000000000000),
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
      (38, 60),
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
      (37, 11)
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
        lower := (exactRationalLiteral (1) 8)
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
            (exactRationalLiteral (7981445021715712001) 1228800000000000000000),
            (exactRationalLiteral (-613957309362747077) 25600000000000000000),
            (exactRationalLiteral (47227485335595929) 1600000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1888869513456449191) 61440000000000000000),
            (exactRationalLiteral (49520718837216049) 1280000000000000000),
            (exactRationalLiteral (-10527161020210937) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-18593786617864082157) 204800000000000000000),
            (exactRationalLiteral (753907763190825283) 12800000000000000000),
            (exactRationalLiteral (35887818852612957) 160000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (56086518670056209831) 1228800000000000000000),
            (exactRationalLiteral (-4209775998702349603) 25600000000000000000),
            (exactRationalLiteral (-282714911620785649) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (19591926874981109329) 1228800000000000000000),
            (exactRationalLiteral (3010901363653832347) 25600000000000000000),
            (exactRationalLiteral (18488735254786613) 320000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-665619177706774453) 76800000000000000000),
            (exactRationalLiteral (-50386377481024709) 1600000000000000000),
            (exactRationalLiteral (-317248232221057) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (333516886475202139) 204800000000000000000),
            (exactRationalLiteral (89801709965979291) 12800000000000000000),
            (exactRationalLiteral (114846488230473) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (218869541113024739) 40960000000000000000),
            (exactRationalLiteral (-2328918578741017) 12800000000000000000),
            (exactRationalLiteral (-53215033281231) 160000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (674430048725156391) 102400000000000000000),
            (exactRationalLiteral (43225867116926243) 6400000000000000000),
            (exactRationalLiteral (1432337445712629) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-11898540856091107901) 614400000000000000000),
            (exactRationalLiteral (-22787146274088731) 2560000000000000000),
            (exactRationalLiteral (-2204014473379397) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-13073488839101703961) 1228800000000000000000),
            (exactRationalLiteral (-225746477160907043) 25600000000000000000),
            (exactRationalLiteral (-10094934820072753) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7606565870125229627) 614400000000000000000),
            (exactRationalLiteral (170790848465918881) 12800000000000000000),
            (exactRationalLiteral (5382141788552819) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (184225069099773493) 1228800000000000000000),
            (exactRationalLiteral (-17947863935142821) 5120000000000000000),
            (exactRationalLiteral (-1369366081705879) 320000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2198664761001160951) 614400000000000000000),
            (exactRationalLiteral (81351026286589739) 12800000000000000000),
            (exactRationalLiteral (85795156667801) 32000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1748851123246852129) 122880000000000000000),
            (exactRationalLiteral (-126408965038230569) 12800000000000000000),
            (exactRationalLiteral (683433422398589) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (27924109069786699289) 614400000000000000000),
            (exactRationalLiteral (-385743204080771741) 12800000000000000000),
            (exactRationalLiteral (10963671304234673) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-38974556992814272159) 1228800000000000000000),
            (exactRationalLiteral (801034213783147131) 25600000000000000000),
            (exactRationalLiteral (-27744834639553351) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-27377183896576083089) 1228800000000000000000),
            (exactRationalLiteral (191792067394980597) 25600000000000000000),
            (exactRationalLiteral (219497621557399) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1612424143267127543) 307200000000000000000),
            (exactRationalLiteral (-7051629378638621) 6400000000000000000),
            (exactRationalLiteral (1070850630685633) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3782426626952281007) 30720000000000000000),
            (exactRationalLiteral (204003779601936381) 3200000000000000000),
            (exactRationalLiteral (-4255118415524623) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (160747314010111232263) 614400000000000000000),
            (exactRationalLiteral (-1760337122429061843) 12800000000000000000),
            (exactRationalLiteral (34642286309432719) 800000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3782426626952281007) 30720000000000000000),
            (exactRationalLiteral (204003779601936381) 3200000000000000000),
            (exactRationalLiteral (-4255118415524623) 200000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1612424143267127543) 307200000000000000000),
            (exactRationalLiteral (-7051629378638621) 6400000000000000000),
            (exactRationalLiteral (1070850630685633) 400000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-27377183896576083089) 1228800000000000000000),
            (exactRationalLiteral (191792067394980597) 25600000000000000000),
            (exactRationalLiteral (219497621557399) 1600000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-38974556992814272159) 1228800000000000000000),
            (exactRationalLiteral (801034213783147131) 25600000000000000000),
            (exactRationalLiteral (-27744834639553351) 1600000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (27924109069786699289) 614400000000000000000),
            (exactRationalLiteral (-385743204080771741) 12800000000000000000),
            (exactRationalLiteral (10963671304234673) 800000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1748851123246852129) 122880000000000000000),
            (exactRationalLiteral (-126408965038230569) 12800000000000000000),
            (exactRationalLiteral (683433422398589) 800000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2198664761001160951) 614400000000000000000),
            (exactRationalLiteral (81351026286589739) 12800000000000000000),
            (exactRationalLiteral (85795156667801) 32000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (184225069099773493) 1228800000000000000000),
            (exactRationalLiteral (-17947863935142821) 5120000000000000000),
            (exactRationalLiteral (-1369366081705879) 320000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7606565870125229627) 614400000000000000000),
            (exactRationalLiteral (170790848465918881) 12800000000000000000),
            (exactRationalLiteral (5382141788552819) 800000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-13073488839101703961) 1228800000000000000000),
            (exactRationalLiteral (-225746477160907043) 25600000000000000000),
            (exactRationalLiteral (-10094934820072753) 1600000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11898540856091107901) 614400000000000000000),
            (exactRationalLiteral (-22787146274088731) 2560000000000000000),
            (exactRationalLiteral (-2204014473379397) 800000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (674430048725156391) 102400000000000000000),
            (exactRationalLiteral (43225867116926243) 6400000000000000000),
            (exactRationalLiteral (1432337445712629) 400000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (218869541113024739) 40960000000000000000),
            (exactRationalLiteral (-2328918578741017) 12800000000000000000),
            (exactRationalLiteral (-53215033281231) 160000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (333516886475202139) 204800000000000000000),
            (exactRationalLiteral (89801709965979291) 12800000000000000000),
            (exactRationalLiteral (114846488230473) 800000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-665619177706774453) 76800000000000000000),
            (exactRationalLiteral (-50386377481024709) 1600000000000000000),
            (exactRationalLiteral (-317248232221057) 100000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (19591926874981109329) 1228800000000000000000),
            (exactRationalLiteral (3010901363653832347) 25600000000000000000),
            (exactRationalLiteral (18488735254786613) 320000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (56086518670056209831) 1228800000000000000000),
            (exactRationalLiteral (-4209775998702349603) 25600000000000000000),
            (exactRationalLiteral (-282714911620785649) 1600000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18593786617864082157) 204800000000000000000),
            (exactRationalLiteral (753907763190825283) 12800000000000000000),
            (exactRationalLiteral (35887818852612957) 160000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1888869513456449191) 61440000000000000000),
            (exactRationalLiteral (49520718837216049) 1280000000000000000),
            (exactRationalLiteral (-10527161020210937) 80000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (7981445021715712001) 1228800000000000000000),
            (exactRationalLiteral (-613957309362747077) 25600000000000000000),
            (exactRationalLiteral (47227485335595929) 1600000000000000000),
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
          (exactRationalLiteral (1246079036162261819) 153600000000000000000),
          (exactRationalLiteral (7839420388222457) 240000000000000000),
          (exactRationalLiteral (2395008733124649903) 25600000000000000000),
          (exactRationalLiteral (8475809523319801709) 153600000000000000000),
          (exactRationalLiteral (150305125865855617) 6400000000000000000),
          (exactRationalLiteral (8506360635618461) 800000000000000000),
          (exactRationalLiteral (264127484437433) 128000000000000000),
          (exactRationalLiteral (411058946573788931) 76800000000000000000),
          (exactRationalLiteral (4213225472049163) 600000000000000000),
          (exactRationalLiteral (63783844457141047) 3200000000000000000),
          (exactRationalLiteral (71786423775515093) 6400000000000000000),
          (exactRationalLiteral (127114631967087491) 9600000000000000000),
          (exactRationalLiteral (53896441988318303) 153600000000000000000),
          (exactRationalLiteral (101480479239090587) 25600000000000000000),
          (exactRationalLiteral (228133828239823811) 15360000000000000000),
          (exactRationalLiteral (727869143953301687) 15360000000000000000),
          (exactRationalLiteral (5182793591161372501) 153600000000000000000),
          (exactRationalLiteral (3493959246977188859) 153600000000000000000),
          (exactRationalLiteral (8491818311551463) 1600000000000000000),
          (exactRationalLiteral (244213395546034837) 1920000000000000000),
          (exactRationalLiteral (6922229041946495767) 25600000000000000000),
          (exactRationalLiteral (244213395546034837) 1920000000000000000),
          (exactRationalLiteral (8491818311551463) 1600000000000000000),
          (exactRationalLiteral (3493959246977188859) 153600000000000000000),
          (exactRationalLiteral (5182793591161372501) 153600000000000000000),
          (exactRationalLiteral (727869143953301687) 15360000000000000000),
          (exactRationalLiteral (228133828239823811) 15360000000000000000),
          (exactRationalLiteral (101480479239090587) 25600000000000000000),
          (exactRationalLiteral (53896441988318303) 153600000000000000000),
          (exactRationalLiteral (127114631967087491) 9600000000000000000),
          (exactRationalLiteral (71786423775515093) 6400000000000000000),
          (exactRationalLiteral (63783844457141047) 3200000000000000000),
          (exactRationalLiteral (4213225472049163) 600000000000000000),
          (exactRationalLiteral (411058946573788931) 76800000000000000000),
          (exactRationalLiteral (264127484437433) 128000000000000000),
          (exactRationalLiteral (8506360635618461) 800000000000000000),
          (exactRationalLiteral (150305125865855617) 6400000000000000000),
          (exactRationalLiteral (8475809523319801709) 153600000000000000000),
          (exactRationalLiteral (2395008733124649903) 25600000000000000000),
          (exactRationalLiteral (7839420388222457) 240000000000000000),
          (exactRationalLiteral (1246079036162261819) 153600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (38, 61),
      (38, 53),
      (38, 45),
      (38, 37),
      (38, 29),
      (38, 21),
      (38, 13),
      (38, 5),
      (37, 61),
      (37, 53),
      (37, 45),
      (37, 37),
      (37, 29),
      (37, 21),
      (37, 13),
      (37, 5),
      (36, 61),
      (36, 53),
      (36, 45),
      (36, 37),
      (36, 29),
      (36, 21),
      (36, 13),
      (36, 5),
      (35, 61),
      (35, 53),
      (35, 45),
      (35, 37),
      (35, 29),
      (35, 21),
      (35, 13),
      (35, 5),
      (34, 61),
      (34, 53),
      (34, 58),
      (35, 2),
      (35, 10),
      (35, 18),
      (35, 26),
      (35, 34),
      (35, 42),
      (35, 50),
      (35, 58),
      (36, 2),
      (36, 10),
      (36, 18),
      (36, 26),
      (36, 34),
      (36, 42),
      (36, 50),
      (36, 58),
      (37, 2),
      (37, 10)
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
theorem generatorCoordinates29_valid : ∀ i, (generatorCoordinates29 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
