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

/-- Actual coordinate interval candidates, block 16. -/
def generatorCoordinates16 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 3
        lower := (exactRationalLiteral (1) 4)
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
            (exactRationalLiteral (29851985859308111219) 9830400000000000000000),
            (exactRationalLiteral (-1297912428665570053) 102400000000000000000),
            (exactRationalLiteral (56430975159372611) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (243767855178139015601) 9830400000000000000000),
            (exactRationalLiteral (922236340127701513) 102400000000000000000),
            (exactRationalLiteral (-249567027437232991) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-95233894957315176317) 1638400000000000000000),
            (exactRationalLiteral (3838648404490773297) 51200000000000000000),
            (exactRationalLiteral (203971882827577881) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (55546299512085524177) 3276800000000000000000),
            (exactRationalLiteral (-14978833207393994661) 102400000000000000000),
            (exactRationalLiteral (-55272374134434969) 640000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (106206741001947290831) 4915200000000000000000),
            (exactRationalLiteral (4875215383686679559) 51200000000000000000),
            (exactRationalLiteral (16706697759195647) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-81538996667578692037) 9830400000000000000000),
            (exactRationalLiteral (-2295865858088455901) 102400000000000000000),
            (exactRationalLiteral (40033744296642251) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (411429354973745213) 1228800000000000000000),
            (exactRationalLiteral (45869086459330933) 12800000000000000000),
            (exactRationalLiteral (-1656585448410643) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-7382863398475585699) 9830400000000000000000),
            (exactRationalLiteral (-134668118346518123) 102400000000000000000),
            (exactRationalLiteral (408104977547113) 640000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4196594964767193247) 9830400000000000000000),
            (exactRationalLiteral (4757374461607173) 20480000000000000000),
            (exactRationalLiteral (-358251419629807) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-142782482656653607) 327680000000000000000),
            (exactRationalLiteral (-7724597510042753) 51200000000000000000),
            (exactRationalLiteral (-364660752429) 12800000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10295353669133671) 393216000000000000000),
            (exactRationalLiteral (2754660144440597) 20480000000000000000),
            (exactRationalLiteral (4401116077601) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (96686400630485719) 98304000000000000000),
            (exactRationalLiteral (14524027245808831) 25600000000000000000),
            (exactRationalLiteral (233605442838463) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-112098271169576333) 1228800000000000000000),
            (exactRationalLiteral (1786953511393391) 12800000000000000000),
            (exactRationalLiteral (-65112392878229) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-28564285946689400903) 3276800000000000000000),
            (exactRationalLiteral (-27287170598425421) 102400000000000000000),
            (exactRationalLiteral (1531846249097979) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-47421705555311702581) 9830400000000000000000),
            (exactRationalLiteral (-45220689409069229) 102400000000000000000),
            (exactRationalLiteral (-841781516504677) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-23822953656034277439) 3276800000000000000000),
            (exactRationalLiteral (35119053511625743) 20480000000000000000),
            (exactRationalLiteral (5501504783178771) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-101939653116720160309) 4915200000000000000000),
            (exactRationalLiteral (-42006278740783293) 51200000000000000000),
            (exactRationalLiteral (3837013471090811) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-151855753456040240033) 2457600000000000000000),
            (exactRationalLiteral (-373901822172462889) 25600000000000000000),
            (exactRationalLiteral (1165206464385539) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-976771973454562826043) 3276800000000000000000),
            (exactRationalLiteral (-28683913176290148297) 102400000000000000000),
            (exactRationalLiteral (85419422542055391) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2097649796667489412319) 4915200000000000000000),
            (exactRationalLiteral (133071846389563861031) 51200000000000000000),
            (exactRationalLiteral (1377424464479650607) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27052277740685664702397) 9830400000000000000000),
            (exactRationalLiteral (-543975098893288930667) 102400000000000000000),
            (exactRationalLiteral (-17576082052013025107) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12350181475223766140957) 2457600000000000000000),
            (exactRationalLiteral (2472089288504059363) 1024000000000000000),
            (exactRationalLiteral (9405241115554658611) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (529356120859454730069) 204800000000000000000),
            (exactRationalLiteral (15396536685746012741) 6400000000000000000),
            (exactRationalLiteral (-2302953846291523413) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-3750129308800972053529) 1638400000000000000000),
            (exactRationalLiteral (-37153077031664775523) 51200000000000000000),
            (exactRationalLiteral (315082188408464013) 64000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3199226575999376514343) 819200000000000000000),
            (exactRationalLiteral (-55679824870343849939) 25600000000000000000),
            (exactRationalLiteral (-914908849084364763) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3750129308800972053529) 1638400000000000000000),
            (exactRationalLiteral (-37153077031664775523) 51200000000000000000),
            (exactRationalLiteral (315082188408464013) 64000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (529356120859454730069) 204800000000000000000),
            (exactRationalLiteral (15396536685746012741) 6400000000000000000),
            (exactRationalLiteral (-2302953846291523413) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-12350181475223766140957) 2457600000000000000000),
            (exactRationalLiteral (2472089288504059363) 1024000000000000000),
            (exactRationalLiteral (9405241115554658611) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (27052277740685664702397) 9830400000000000000000),
            (exactRationalLiteral (-543975098893288930667) 102400000000000000000),
            (exactRationalLiteral (-17576082052013025107) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2097649796667489412319) 4915200000000000000000),
            (exactRationalLiteral (133071846389563861031) 51200000000000000000),
            (exactRationalLiteral (1377424464479650607) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-976771973454562826043) 3276800000000000000000),
            (exactRationalLiteral (-28683913176290148297) 102400000000000000000),
            (exactRationalLiteral (85419422542055391) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-151855753456040240033) 2457600000000000000000),
            (exactRationalLiteral (-373901822172462889) 25600000000000000000),
            (exactRationalLiteral (1165206464385539) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-101939653116720160309) 4915200000000000000000),
            (exactRationalLiteral (-42006278740783293) 51200000000000000000),
            (exactRationalLiteral (3837013471090811) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-23822953656034277439) 3276800000000000000000),
            (exactRationalLiteral (35119053511625743) 20480000000000000000),
            (exactRationalLiteral (5501504783178771) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-47421705555311702581) 9830400000000000000000),
            (exactRationalLiteral (-45220689409069229) 102400000000000000000),
            (exactRationalLiteral (-841781516504677) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-28564285946689400903) 3276800000000000000000),
            (exactRationalLiteral (-27287170598425421) 102400000000000000000),
            (exactRationalLiteral (1531846249097979) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-112098271169576333) 1228800000000000000000),
            (exactRationalLiteral (1786953511393391) 12800000000000000000),
            (exactRationalLiteral (-65112392878229) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (96686400630485719) 98304000000000000000),
            (exactRationalLiteral (14524027245808831) 25600000000000000000),
            (exactRationalLiteral (233605442838463) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-10295353669133671) 393216000000000000000),
            (exactRationalLiteral (2754660144440597) 20480000000000000000),
            (exactRationalLiteral (4401116077601) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-142782482656653607) 327680000000000000000),
            (exactRationalLiteral (-7724597510042753) 51200000000000000000),
            (exactRationalLiteral (-364660752429) 12800000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4196594964767193247) 9830400000000000000000),
            (exactRationalLiteral (4757374461607173) 20480000000000000000),
            (exactRationalLiteral (-358251419629807) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-7382863398475585699) 9830400000000000000000),
            (exactRationalLiteral (-134668118346518123) 102400000000000000000),
            (exactRationalLiteral (408104977547113) 640000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (411429354973745213) 1228800000000000000000),
            (exactRationalLiteral (45869086459330933) 12800000000000000000),
            (exactRationalLiteral (-1656585448410643) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-81538996667578692037) 9830400000000000000000),
            (exactRationalLiteral (-2295865858088455901) 102400000000000000000),
            (exactRationalLiteral (40033744296642251) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (106206741001947290831) 4915200000000000000000),
            (exactRationalLiteral (4875215383686679559) 51200000000000000000),
            (exactRationalLiteral (16706697759195647) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (55546299512085524177) 3276800000000000000000),
            (exactRationalLiteral (-14978833207393994661) 102400000000000000000),
            (exactRationalLiteral (-55272374134434969) 640000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-95233894957315176317) 1638400000000000000000),
            (exactRationalLiteral (3838648404490773297) 51200000000000000000),
            (exactRationalLiteral (203971882827577881) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (243767855178139015601) 9830400000000000000000),
            (exactRationalLiteral (922236340127701513) 102400000000000000000),
            (exactRationalLiteral (-249567027437232991) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (29851985859308111219) 9830400000000000000000),
            (exactRationalLiteral (-1297912428665570053) 102400000000000000000),
            (exactRationalLiteral (56430975159372611) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (22081685931928413) 6400000000000000000),
          (exactRationalLiteral (10241688433261072439) 409600000000000000000),
          (exactRationalLiteral (193090907490303027) 3200000000000000000),
          (exactRationalLiteral (411521715146819011) 19200000000000000000),
          (exactRationalLiteral (15108140109483563891) 614400000000000000000),
          (exactRationalLiteral (3678831785019172531) 409600000000000000000),
          (exactRationalLiteral (67951182834849601) 153600000000000000000),
          (exactRationalLiteral (194497384853896019) 245760000000000000000),
          (exactRationalLiteral (8337480462669799) 19200000000000000000),
          (exactRationalLiteral (270626822038896269) 614400000000000000000),
          (exactRationalLiteral (194451355081189) 6400000000000000000),
          (exactRationalLiteral (102559336082407429) 102400000000000000000),
          (exactRationalLiteral (30642666950299) 320000000000000000),
          (exactRationalLiteral (10721287690887022009) 1228800000000000000000),
          (exactRationalLiteral (5944964783944220953) 1228800000000000000000),
          (exactRationalLiteral (140584089626072281) 19200000000000000000),
          (exactRationalLiteral (4252247386405488507) 204800000000000000000),
          (exactRationalLiteral (764796421600930597) 12288000000000000000),
          (exactRationalLiteral (75400983959391903041) 245760000000000000000),
          (exactRationalLiteral (104195372158211014473) 204800000000000000000),
          (exactRationalLiteral (18639094507095591719) 6400000000000000000),
          (exactRationalLiteral (1628477145957522607) 320000000000000000),
          (exactRationalLiteral (2542937750323087489) 960000000000000000),
          (exactRationalLiteral (1417331570723595752191) 614400000000000000000),
          (exactRationalLiteral (19066195560488527537) 4800000000000000000),
          (exactRationalLiteral (1417331570723595752191) 614400000000000000000),
          (exactRationalLiteral (2542937750323087489) 960000000000000000),
          (exactRationalLiteral (1628477145957522607) 320000000000000000),
          (exactRationalLiteral (18639094507095591719) 6400000000000000000),
          (exactRationalLiteral (104195372158211014473) 204800000000000000000),
          (exactRationalLiteral (75400983959391903041) 245760000000000000000),
          (exactRationalLiteral (764796421600930597) 12288000000000000000),
          (exactRationalLiteral (4252247386405488507) 204800000000000000000),
          (exactRationalLiteral (140584089626072281) 19200000000000000000),
          (exactRationalLiteral (5944964783944220953) 1228800000000000000000),
          (exactRationalLiteral (10721287690887022009) 1228800000000000000000),
          (exactRationalLiteral (30642666950299) 320000000000000000),
          (exactRationalLiteral (102559336082407429) 102400000000000000000),
          (exactRationalLiteral (194451355081189) 6400000000000000000),
          (exactRationalLiteral (270626822038896269) 614400000000000000000),
          (exactRationalLiteral (8337480462669799) 19200000000000000000),
          (exactRationalLiteral (194497384853896019) 245760000000000000000),
          (exactRationalLiteral (67951182834849601) 153600000000000000000),
          (exactRationalLiteral (3678831785019172531) 409600000000000000000),
          (exactRationalLiteral (15108140109483563891) 614400000000000000000),
          (exactRationalLiteral (411521715146819011) 19200000000000000000),
          (exactRationalLiteral (193090907490303027) 3200000000000000000),
          (exactRationalLiteral (10241688433261072439) 409600000000000000000),
          (exactRationalLiteral (22081685931928413) 6400000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 36),
      (30, 20),
      (30, 4),
      (29, 52),
      (29, 36),
      (29, 20),
      (29, 4),
      (28, 52),
      (28, 36),
      (28, 20),
      (28, 4),
      (27, 52),
      (27, 36),
      (27, 20),
      (27, 4),
      (26, 52),
      (26, 36),
      (26, 20),
      (26, 4),
      (25, 52),
      (25, 36),
      (25, 20),
      (25, 4),
      (24, 52),
      (24, 36),
      (24, 20),
      (24, 4),
      (23, 52),
      (23, 36),
      (23, 20),
      (23, 27),
      (23, 43),
      (23, 59),
      (24, 11),
      (24, 27),
      (24, 43),
      (24, 59),
      (25, 11),
      (25, 27),
      (25, 43),
      (25, 59),
      (26, 11),
      (26, 27),
      (26, 43),
      (26, 59),
      (27, 11),
      (27, 27),
      (27, 43),
      (27, 59),
      (28, 11),
      (28, 27),
      (28, 43),
      (28, 59)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 3
        lower := (exactRationalLiteral (5) 16)
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
            (exactRationalLiteral (7574018274651445659) 3276800000000000000000),
            (exactRationalLiteral (-1082002610664492237) 102400000000000000000),
            (exactRationalLiteral (51523933841166297) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (246423743146100967739) 9830400000000000000000),
            (exactRationalLiteral (-695785655998439) 4096000000000000000),
            (exactRationalLiteral (-220248463326598253) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-86788925368569093471) 1638400000000000000000),
            (exactRationalLiteral (4582213808482421913) 51200000000000000000),
            (exactRationalLiteral (167810819168246427) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (73827111973832093201) 9830400000000000000000),
            (exactRationalLiteral (-15895503125079900653) 102400000000000000000),
            (exactRationalLiteral (-181973088170778151) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (45173140904615491127) 1638400000000000000000),
            (exactRationalLiteral (4872496693057840863) 51200000000000000000),
            (exactRationalLiteral (-3613208614722999) 320000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-94717545536597782487) 9830400000000000000000),
            (exactRationalLiteral (-83104408277036717) 4096000000000000000),
            (exactRationalLiteral (69094081284626737) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (132621137145425779) 245760000000000000000),
            (exactRationalLiteral (37413163354851261) 12800000000000000000),
            (exactRationalLiteral (-2571376103829193) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-2719859844111042251) 3276800000000000000000),
            (exactRationalLiteral (-123102880011205411) 102400000000000000000),
            (exactRationalLiteral (3742094279920791) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4060095460460561141) 9830400000000000000000),
            (exactRationalLiteral (21392510376503937) 102400000000000000000),
            (exactRationalLiteral (-838929546136157) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2188366185231319427) 4915200000000000000000),
            (exactRationalLiteral (-1554822496512981) 10240000000000000000),
            (exactRationalLiteral (20825107792549) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-58265765712761879) 3276800000000000000000),
            (exactRationalLiteral (13737868618466897) 102400000000000000000),
            (exactRationalLiteral (-4423433589129) 640000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2507036661748605029) 2457600000000000000000),
            (exactRationalLiteral (15423057615936439) 25600000000000000000),
            (exactRationalLiteral (215909742225341) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-34016973720566333) 409600000000000000000),
            (exactRationalLiteral (1579992766908343) 12800000000000000000),
            (exactRationalLiteral (-7673595872859) 80000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-85839620420509507783) 9830400000000000000000),
            (exactRationalLiteral (-21870641521997653) 102400000000000000000),
            (exactRationalLiteral (235283657823181) 640000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-15900577832562306893) 3276800000000000000000),
            (exactRationalLiteral (-47889029336461237) 102400000000000000000),
            (exactRationalLiteral (-492388447191327) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-70349978248385308991) 9830400000000000000000),
            (exactRationalLiteral (197247815176146691) 102400000000000000000),
            (exactRationalLiteral (5324769025830217) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-102143857517131661639) 4915200000000000000000),
            (exactRationalLiteral (-25763669666365701) 51200000000000000000),
            (exactRationalLiteral (856858213223597) 320000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-154023679957966075307) 2457600000000000000000),
            (exactRationalLiteral (-347811671261847249) 25600000000000000000),
            (exactRationalLiteral (57752345067041) 6400000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-3100818020356871621563) 9830400000000000000000),
            (exactRationalLiteral (-5610812497819077181) 20480000000000000000),
            (exactRationalLiteral (45901184211065161) 640000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2910140549118183586741) 4915200000000000000000),
            (exactRationalLiteral (27469366903452012787) 10240000000000000000),
            (exactRationalLiteral (152013919873690169) 320000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1572807945945805541777) 655360000000000000000),
            (exactRationalLiteral (-606976913858686876323) 102400000000000000000),
            (exactRationalLiteral (-13924825430685947721) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3957282976350188432629) 819200000000000000000),
            (exactRationalLiteral (96751326430288136163) 25600000000000000000),
            (exactRationalLiteral (8069305993288667433) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1653860529417728663849) 614400000000000000000),
            (exactRationalLiteral (1341783548154651633) 1280000000000000000),
            (exactRationalLiteral (-16326845009558831) 1600000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-11382274311442288260601) 4915200000000000000000),
            (exactRationalLiteral (-7391147876779699611) 51200000000000000000),
            (exactRationalLiteral (7003909867230937631) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9253280665321309263143) 2457600000000000000000),
            (exactRationalLiteral (-59010063899553710539) 25600000000000000000),
            (exactRationalLiteral (-750210665520565537) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-11382274311442288260601) 4915200000000000000000),
            (exactRationalLiteral (-7391147876779699611) 51200000000000000000),
            (exactRationalLiteral (7003909867230937631) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1653860529417728663849) 614400000000000000000),
            (exactRationalLiteral (1341783548154651633) 1280000000000000000),
            (exactRationalLiteral (-16326845009558831) 1600000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-3957282976350188432629) 819200000000000000000),
            (exactRationalLiteral (96751326430288136163) 25600000000000000000),
            (exactRationalLiteral (8069305993288667433) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1572807945945805541777) 655360000000000000000),
            (exactRationalLiteral (-606976913858686876323) 102400000000000000000),
            (exactRationalLiteral (-13924825430685947721) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2910140549118183586741) 4915200000000000000000),
            (exactRationalLiteral (27469366903452012787) 10240000000000000000),
            (exactRationalLiteral (152013919873690169) 320000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3100818020356871621563) 9830400000000000000000),
            (exactRationalLiteral (-5610812497819077181) 20480000000000000000),
            (exactRationalLiteral (45901184211065161) 640000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-154023679957966075307) 2457600000000000000000),
            (exactRationalLiteral (-347811671261847249) 25600000000000000000),
            (exactRationalLiteral (57752345067041) 6400000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-102143857517131661639) 4915200000000000000000),
            (exactRationalLiteral (-25763669666365701) 51200000000000000000),
            (exactRationalLiteral (856858213223597) 320000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-70349978248385308991) 9830400000000000000000),
            (exactRationalLiteral (197247815176146691) 102400000000000000000),
            (exactRationalLiteral (5324769025830217) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-15900577832562306893) 3276800000000000000000),
            (exactRationalLiteral (-47889029336461237) 102400000000000000000),
            (exactRationalLiteral (-492388447191327) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-85839620420509507783) 9830400000000000000000),
            (exactRationalLiteral (-21870641521997653) 102400000000000000000),
            (exactRationalLiteral (235283657823181) 640000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-34016973720566333) 409600000000000000000),
            (exactRationalLiteral (1579992766908343) 12800000000000000000),
            (exactRationalLiteral (-7673595872859) 80000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2507036661748605029) 2457600000000000000000),
            (exactRationalLiteral (15423057615936439) 25600000000000000000),
            (exactRationalLiteral (215909742225341) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-58265765712761879) 3276800000000000000000),
            (exactRationalLiteral (13737868618466897) 102400000000000000000),
            (exactRationalLiteral (-4423433589129) 640000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2188366185231319427) 4915200000000000000000),
            (exactRationalLiteral (-1554822496512981) 10240000000000000000),
            (exactRationalLiteral (20825107792549) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4060095460460561141) 9830400000000000000000),
            (exactRationalLiteral (21392510376503937) 102400000000000000000),
            (exactRationalLiteral (-838929546136157) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2719859844111042251) 3276800000000000000000),
            (exactRationalLiteral (-123102880011205411) 102400000000000000000),
            (exactRationalLiteral (3742094279920791) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (132621137145425779) 245760000000000000000),
            (exactRationalLiteral (37413163354851261) 12800000000000000000),
            (exactRationalLiteral (-2571376103829193) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-94717545536597782487) 9830400000000000000000),
            (exactRationalLiteral (-83104408277036717) 4096000000000000000),
            (exactRationalLiteral (69094081284626737) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (45173140904615491127) 1638400000000000000000),
            (exactRationalLiteral (4872496693057840863) 51200000000000000000),
            (exactRationalLiteral (-3613208614722999) 320000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (73827111973832093201) 9830400000000000000000),
            (exactRationalLiteral (-15895503125079900653) 102400000000000000000),
            (exactRationalLiteral (-181973088170778151) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-86788925368569093471) 1638400000000000000000),
            (exactRationalLiteral (4582213808482421913) 51200000000000000000),
            (exactRationalLiteral (167810819168246427) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (246423743146100967739) 9830400000000000000000),
            (exactRationalLiteral (-695785655998439) 4096000000000000000),
            (exactRationalLiteral (-220248463326598253) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7574018274651445659) 3276800000000000000000),
            (exactRationalLiteral (-1082002610664492237) 102400000000000000000),
            (exactRationalLiteral (51523933841166297) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (3265635997266301967) 1228800000000000000000),
          (exactRationalLiteral (5139084281935059257) 204800000000000000000),
          (exactRationalLiteral (11399662689242505881) 204800000000000000000),
          (exactRationalLiteral (3023012692332719059) 245760000000000000000),
          (exactRationalLiteral (2344770754584105401) 76800000000000000000),
          (exactRationalLiteral (1573883808516057247) 153600000000000000000),
          (exactRationalLiteral (11987088314882591) 19200000000000000000),
          (exactRationalLiteral (1064601388103861) 1228800000000000000),
          (exactRationalLiteral (171939560048551177) 409600000000000000000),
          (exactRationalLiteral (11518712726587049) 25600000000000000000),
          (exactRationalLiteral (5401599883887791) 245760000000000000000),
          (exactRationalLiteral (39905386187074747) 38400000000000000000),
          (exactRationalLiteral (2672984390181847) 30720000000000000000),
          (exactRationalLiteral (447405629188479917) 51200000000000000000),
          (exactRationalLiteral (747604735226612839) 153600000000000000000),
          (exactRationalLiteral (8865707377369698017) 1228800000000000000000),
          (exactRationalLiteral (63880045008834307) 3072000000000000000),
          (exactRationalLiteral (2422574395889777351) 38400000000000000000),
          (exactRationalLiteral (16584477327144453993) 51200000000000000000),
          (exactRationalLiteral (2077595365022195957) 3072000000000000000),
          (exactRationalLiteral (3171181228270052796721) 1228800000000000000000),
          (exactRationalLiteral (1517153377850053838561) 307200000000000000000),
          (exactRationalLiteral (17374955884078252203) 6400000000000000000),
          (exactRationalLiteral (356132274898900267703) 153600000000000000000),
          (exactRationalLiteral (1178497234491453349817) 307200000000000000000),
          (exactRationalLiteral (356132274898900267703) 153600000000000000000),
          (exactRationalLiteral (17374955884078252203) 6400000000000000000),
          (exactRationalLiteral (1517153377850053838561) 307200000000000000000),
          (exactRationalLiteral (3171181228270052796721) 1228800000000000000000),
          (exactRationalLiteral (2077595365022195957) 3072000000000000000),
          (exactRationalLiteral (16584477327144453993) 51200000000000000000),
          (exactRationalLiteral (2422574395889777351) 38400000000000000000),
          (exactRationalLiteral (63880045008834307) 3072000000000000000),
          (exactRationalLiteral (8865707377369698017) 1228800000000000000000),
          (exactRationalLiteral (747604735226612839) 153600000000000000000),
          (exactRationalLiteral (447405629188479917) 51200000000000000000),
          (exactRationalLiteral (2672984390181847) 30720000000000000000),
          (exactRationalLiteral (39905386187074747) 38400000000000000000),
          (exactRationalLiteral (5401599883887791) 245760000000000000000),
          (exactRationalLiteral (11518712726587049) 25600000000000000000),
          (exactRationalLiteral (171939560048551177) 409600000000000000000),
          (exactRationalLiteral (1064601388103861) 1228800000000000000),
          (exactRationalLiteral (11987088314882591) 19200000000000000000),
          (exactRationalLiteral (1573883808516057247) 153600000000000000000),
          (exactRationalLiteral (2344770754584105401) 76800000000000000000),
          (exactRationalLiteral (3023012692332719059) 245760000000000000000),
          (exactRationalLiteral (11399662689242505881) 204800000000000000000),
          (exactRationalLiteral (5139084281935059257) 204800000000000000000),
          (exactRationalLiteral (3265635997266301967) 1228800000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 37),
      (30, 21),
      (30, 5),
      (29, 53),
      (29, 37),
      (29, 21),
      (29, 5),
      (28, 53),
      (28, 37),
      (28, 21),
      (28, 5),
      (27, 53),
      (27, 37),
      (27, 21),
      (27, 5),
      (26, 53),
      (26, 37),
      (26, 21),
      (26, 5),
      (25, 53),
      (25, 37),
      (25, 21),
      (25, 5),
      (24, 53),
      (24, 37),
      (24, 21),
      (24, 5),
      (23, 53),
      (23, 37),
      (23, 21),
      (23, 26),
      (23, 42),
      (23, 58),
      (24, 10),
      (24, 26),
      (24, 42),
      (24, 58),
      (25, 10),
      (25, 26),
      (25, 42),
      (25, 58),
      (26, 10),
      (26, 26),
      (26, 42),
      (26, 58),
      (27, 10),
      (27, 26),
      (27, 42),
      (27, 58),
      (28, 10),
      (28, 26),
      (28, 42),
      (28, 58)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 3
        lower := (exactRationalLiteral (3) 8)
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
            (exactRationalLiteral (16828698200788553863) 9830400000000000000000),
            (exactRationalLiteral (-885720957936239677) 102400000000000000000),
            (exactRationalLiteral (46616892522959983) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16252911199614970787) 655360000000000000000),
            (exactRationalLiteral (-839751366485084511) 102400000000000000000),
            (exactRationalLiteral (-38185979843192703) 640000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-77001469226477039209) 1638400000000000000000),
            (exactRationalLiteral (5181134957836744713) 51200000000000000000),
            (exactRationalLiteral (131649755508914973) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-23352028704691061753) 9830400000000000000000),
            (exactRationalLiteral (-16434617912760219869) 102400000000000000000),
            (exactRationalLiteral (-87584305669381457) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (164398519391978896051) 4915200000000000000000),
            (exactRationalLiteral (4730687039097759599) 51200000000000000000),
            (exactRationalLiteral (-52838783906425637) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-35412612151595277083) 3276800000000000000000),
            (exactRationalLiteral (-348622641562288401) 20480000000000000000),
            (exactRationalLiteral (98154418272611223) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (170613797997722389) 245760000000000000000),
            (exactRationalLiteral (25298077628697389) 12800000000000000000),
            (exactRationalLiteral (-3486166759247743) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-8846485403472568823) 9830400000000000000000),
            (exactRationalLiteral (-20946272821430359) 20480000000000000000),
            (exactRationalLiteral (5443663672106017) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1314576755087065601) 3276800000000000000000),
            (exactRationalLiteral (17075435938946609) 102400000000000000000),
            (exactRationalLiteral (-1319607672642507) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2234495328025813573) 4915200000000000000000),
            (exactRationalLiteral (-7557996647702361) 51200000000000000000),
            (exactRationalLiteral (87232809638723) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-92741564578924979) 9830400000000000000000),
            (exactRationalLiteral (543854535145513) 4096000000000000000),
            (exactRationalLiteral (-48635451968891) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (867365047182825089) 819200000000000000000),
            (exactRationalLiteral (16251305183611559) 25600000000000000000),
            (exactRationalLiteral (198214041612219) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-18584880531712949) 245760000000000000000),
            (exactRationalLiteral (1480009676479031) 12800000000000000000),
            (exactRationalLiteral (-11623565850361) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-85958148962012031137) 9830400000000000000000),
            (exactRationalLiteral (-17875824285498181) 102400000000000000000),
            (exactRationalLiteral (820990329133831) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-76789726020471569) 15728640000000000000),
            (exactRationalLiteral (-9831959397319969) 20480000000000000000),
            (exactRationalLiteral (-142995377877977) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-69103301072047860457) 9830400000000000000000),
            (exactRationalLiteral (218193419764770451) 102400000000000000000),
            (exactRationalLiteral (5148033268481663) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-34081746310652110443) 1638400000000000000000),
            (exactRationalLiteral (-7731950211839413) 51200000000000000000),
            (exactRationalLiteral (4731568661145159) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-156018349424690787581) 2457600000000000000000),
            (exactRationalLiteral (-316149477105421889) 25600000000000000000),
            (exactRationalLiteral (1722410788966511) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-3265811978244726945677) 9830400000000000000000),
            (exactRationalLiteral (-26847865807847541857) 102400000000000000000),
            (exactRationalLiteral (373592419568596219) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1246957657317906860481) 1638400000000000000000),
            (exactRationalLiteral (139152403184511467791) 51200000000000000000),
            (exactRationalLiteral (142714734257251083) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (19797764827352038805609) 9830400000000000000000),
            (exactRationalLiteral (-131074740467755302487) 20480000000000000000),
            (exactRationalLiteral (-2054713761871774067) 640000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-447994121561537457457) 98304000000000000000),
            (exactRationalLiteral (126356680158910823539) 25600000000000000000),
            (exactRationalLiteral (1346674174204535251) 160000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1670672161228416644491) 614400000000000000000),
            (exactRationalLiteral (-930308323812818259) 6400000000000000000),
            (exactRationalLiteral (-1778757406098184337) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-11346066859668117857471) 4915200000000000000000),
            (exactRationalLiteral (755128076247309021) 2048000000000000000),
            (exactRationalLiteral (6130765024250274937) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8890876546671995410369) 2457600000000000000000),
            (exactRationalLiteral (-12336302038901674847) 5120000000000000000),
            (exactRationalLiteral (-585512481956766311) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-11346066859668117857471) 4915200000000000000000),
            (exactRationalLiteral (755128076247309021) 2048000000000000000),
            (exactRationalLiteral (6130765024250274937) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1670672161228416644491) 614400000000000000000),
            (exactRationalLiteral (-930308323812818259) 6400000000000000000),
            (exactRationalLiteral (-1778757406098184337) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-447994121561537457457) 98304000000000000000),
            (exactRationalLiteral (126356680158910823539) 25600000000000000000),
            (exactRationalLiteral (1346674174204535251) 160000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (19797764827352038805609) 9830400000000000000000),
            (exactRationalLiteral (-131074740467755302487) 20480000000000000000),
            (exactRationalLiteral (-2054713761871774067) 640000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1246957657317906860481) 1638400000000000000000),
            (exactRationalLiteral (139152403184511467791) 51200000000000000000),
            (exactRationalLiteral (142714734257251083) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3265811978244726945677) 9830400000000000000000),
            (exactRationalLiteral (-26847865807847541857) 102400000000000000000),
            (exactRationalLiteral (373592419568596219) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-156018349424690787581) 2457600000000000000000),
            (exactRationalLiteral (-316149477105421889) 25600000000000000000),
            (exactRationalLiteral (1722410788966511) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-34081746310652110443) 1638400000000000000000),
            (exactRationalLiteral (-7731950211839413) 51200000000000000000),
            (exactRationalLiteral (4731568661145159) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-69103301072047860457) 9830400000000000000000),
            (exactRationalLiteral (218193419764770451) 102400000000000000000),
            (exactRationalLiteral (5148033268481663) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-76789726020471569) 15728640000000000000),
            (exactRationalLiteral (-9831959397319969) 20480000000000000000),
            (exactRationalLiteral (-142995377877977) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-85958148962012031137) 9830400000000000000000),
            (exactRationalLiteral (-17875824285498181) 102400000000000000000),
            (exactRationalLiteral (820990329133831) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18584880531712949) 245760000000000000000),
            (exactRationalLiteral (1480009676479031) 12800000000000000000),
            (exactRationalLiteral (-11623565850361) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (867365047182825089) 819200000000000000000),
            (exactRationalLiteral (16251305183611559) 25600000000000000000),
            (exactRationalLiteral (198214041612219) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-92741564578924979) 9830400000000000000000),
            (exactRationalLiteral (543854535145513) 4096000000000000000),
            (exactRationalLiteral (-48635451968891) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2234495328025813573) 4915200000000000000000),
            (exactRationalLiteral (-7557996647702361) 51200000000000000000),
            (exactRationalLiteral (87232809638723) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1314576755087065601) 3276800000000000000000),
            (exactRationalLiteral (17075435938946609) 102400000000000000000),
            (exactRationalLiteral (-1319607672642507) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-8846485403472568823) 9830400000000000000000),
            (exactRationalLiteral (-20946272821430359) 20480000000000000000),
            (exactRationalLiteral (5443663672106017) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (170613797997722389) 245760000000000000000),
            (exactRationalLiteral (25298077628697389) 12800000000000000000),
            (exactRationalLiteral (-3486166759247743) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-35412612151595277083) 3276800000000000000000),
            (exactRationalLiteral (-348622641562288401) 20480000000000000000),
            (exactRationalLiteral (98154418272611223) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (164398519391978896051) 4915200000000000000000),
            (exactRationalLiteral (4730687039097759599) 51200000000000000000),
            (exactRationalLiteral (-52838783906425637) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-23352028704691061753) 9830400000000000000000),
            (exactRationalLiteral (-16434617912760219869) 102400000000000000000),
            (exactRationalLiteral (-87584305669381457) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-77001469226477039209) 1638400000000000000000),
            (exactRationalLiteral (5181134957836744713) 51200000000000000000),
            (exactRationalLiteral (131649755508914973) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (16252911199614970787) 655360000000000000000),
            (exactRationalLiteral (-839751366485084511) 102400000000000000000),
            (exactRationalLiteral (-38185979843192703) 640000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16828698200788553863) 9830400000000000000000),
            (exactRationalLiteral (-885720957936239677) 102400000000000000000),
            (exactRationalLiteral (46616892522959983) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (2453520659103157) 1228800000000000000),
          (exactRationalLiteral (3839460517405884491) 153600000000000000000),
          (exactRationalLiteral (256390398702692647) 5120000000000000000),
          (exactRationalLiteral (9108930121091145923) 1228800000000000000000),
          (exactRationalLiteral (7433944907797353859) 204800000000000000000),
          (exactRationalLiteral (13894772831863541419) 1228800000000000000000),
          (exactRationalLiteral (114755915908656451) 153600000000000000000),
          (exactRationalLiteral (380979071670067231) 409600000000000000000),
          (exactRationalLiteral (62479297766136109) 153600000000000000000),
          (exactRationalLiteral (11284372078445407) 24576000000000000000),
          (exactRationalLiteral (2088489092636461) 153600000000000000000),
          (exactRationalLiteral (66285871284346001) 61440000000000000000),
          (exactRationalLiteral (761036520252421) 9600000000000000000),
          (exactRationalLiteral (10751186397232639403) 1228800000000000000000),
          (exactRationalLiteral (2005888018473062809) 409600000000000000000),
          (exactRationalLiteral (363241400331552357) 51200000000000000000),
          (exactRationalLiteral (6391120380601676843) 307200000000000000000),
          (exactRationalLiteral (19617533148595853671) 307200000000000000000),
          (exactRationalLiteral (418145344395038393423) 1228800000000000000000),
          (exactRationalLiteral (519806206034683892273) 614400000000000000000),
          (exactRationalLiteral (339550618744212940519) 153600000000000000000),
          (exactRationalLiteral (180594609364702623167) 38400000000000000000),
          (exactRationalLiteral (52297258627136749433) 19200000000000000000),
          (exactRationalLiteral (59291003114023046239) 25600000000000000000),
          (exactRationalLiteral (47260844743322230909) 12800000000000000000),
          (exactRationalLiteral (59291003114023046239) 25600000000000000000),
          (exactRationalLiteral (52297258627136749433) 19200000000000000000),
          (exactRationalLiteral (180594609364702623167) 38400000000000000000),
          (exactRationalLiteral (339550618744212940519) 153600000000000000000),
          (exactRationalLiteral (519806206034683892273) 614400000000000000000),
          (exactRationalLiteral (418145344395038393423) 1228800000000000000000),
          (exactRationalLiteral (19617533148595853671) 307200000000000000000),
          (exactRationalLiteral (6391120380601676843) 307200000000000000000),
          (exactRationalLiteral (363241400331552357) 51200000000000000000),
          (exactRationalLiteral (2005888018473062809) 409600000000000000000),
          (exactRationalLiteral (10751186397232639403) 1228800000000000000000),
          (exactRationalLiteral (761036520252421) 9600000000000000000),
          (exactRationalLiteral (66285871284346001) 61440000000000000000),
          (exactRationalLiteral (2088489092636461) 153600000000000000000),
          (exactRationalLiteral (11284372078445407) 24576000000000000000),
          (exactRationalLiteral (62479297766136109) 153600000000000000000),
          (exactRationalLiteral (380979071670067231) 409600000000000000000),
          (exactRationalLiteral (114755915908656451) 153600000000000000000),
          (exactRationalLiteral (13894772831863541419) 1228800000000000000000),
          (exactRationalLiteral (7433944907797353859) 204800000000000000000),
          (exactRationalLiteral (9108930121091145923) 1228800000000000000000),
          (exactRationalLiteral (256390398702692647) 5120000000000000000),
          (exactRationalLiteral (3839460517405884491) 153600000000000000000),
          (exactRationalLiteral (2453520659103157) 1228800000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 38),
      (30, 22),
      (30, 6),
      (29, 54),
      (29, 38),
      (29, 22),
      (29, 6),
      (28, 54),
      (28, 38),
      (28, 22),
      (28, 6),
      (27, 54),
      (27, 38),
      (27, 22),
      (27, 6),
      (26, 54),
      (26, 38),
      (26, 22),
      (26, 6),
      (25, 54),
      (25, 38),
      (25, 22),
      (25, 6),
      (24, 54),
      (24, 38),
      (24, 22),
      (24, 6),
      (23, 54),
      (23, 38),
      (23, 22),
      (23, 25),
      (23, 41),
      (23, 57),
      (24, 9),
      (24, 25),
      (24, 41),
      (24, 57),
      (25, 9),
      (25, 25),
      (25, 41),
      (25, 57),
      (26, 9),
      (26, 25),
      (26, 41),
      (26, 57),
      (27, 9),
      (27, 25),
      (27, 41),
      (27, 57),
      (28, 9),
      (28, 25),
      (28, 41),
      (28, 57)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 3
        lower := (exactRationalLiteral (7) 16)
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
            (exactRationalLiteral (12054146998173810341) 9830400000000000000000),
            (exactRationalLiteral (-709067470480812373) 102400000000000000000),
            (exactRationalLiteral (41709851204753669) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (236581275261165031511) 9830400000000000000000),
            (exactRationalLiteral (-308966767025533819) 20480000000000000000),
            (exactRationalLiteral (-161611335105328777) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-66160815040313665163) 1638400000000000000000),
            (exactRationalLiteral (5635411852553741697) 51200000000000000000),
            (exactRationalLiteral (95488691849583519) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1635109236257058289) 131072000000000000000),
            (exactRationalLiteral (-16596177570434952309) 102400000000000000000),
            (exactRationalLiteral (6804476832015237) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (192009485256357103433) 4915200000000000000000),
            (exactRationalLiteral (4449786421806435767) 51200000000000000000),
            (exactRationalLiteral (-87611524739236279) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-115402421334431210659) 9830400000000000000000),
            (exactRationalLiteral (-1292374860745028141) 102400000000000000000),
            (exactRationalLiteral (127214755260595709) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (959364292028149163) 1228800000000000000000),
            (exactRationalLiteral (9523829280869317) 12800000000000000000),
            (exactRationalLiteral (-4400957414666293) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-1880548669296293297) 1966080000000000000000),
            (exactRationalLiteral (-3182142825374291) 4096000000000000000),
            (exactRationalLiteral (7145233064291243) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3859035654205252633) 9830400000000000000000),
            (exactRationalLiteral (10835648995363881) 102400000000000000000),
            (exactRationalLiteral (-1800285799148857) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-759510294462992789) 1638400000000000000000),
            (exactRationalLiteral (-7076250005455121) 51200000000000000000),
            (exactRationalLiteral (153640511484897) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2370616573363541) 1966080000000000000000),
            (exactRationalLiteral (13348785002715769) 102400000000000000000),
            (exactRationalLiteral (-75153735992137) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2701910758347038761) 2457600000000000000000),
            (exactRationalLiteral (17008769948834191) 25600000000000000000),
            (exactRationalLiteral (180518340999097) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-16815369947167831) 245760000000000000000),
            (exactRationalLiteral (297400848021091) 2560000000000000000),
            (exactRationalLiteral (15120847663573) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-28685657911871780849) 3276800000000000000000),
            (exactRationalLiteral (-3060543777785401) 20480000000000000000),
            (exactRationalLiteral (465562369151757) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-48288855916971612019) 9830400000000000000000),
            (exactRationalLiteral (-49032992359485053) 102400000000000000000),
            (exactRationalLiteral (206397691435373) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-22577690365755617337) 3276800000000000000000),
            (exactRationalLiteral (47686416264799999) 20480000000000000000),
            (exactRationalLiteral (4971297511133109) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-102233062698913517203) 4915200000000000000000),
            (exactRationalLiteral (12088879622795571) 51200000000000000000),
            (exactRationalLiteral (5178846256172333) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-31561265919347903707) 491520000000000000000),
            (exactRationalLiteral (-278915239703186809) 25600000000000000000),
            (exactRationalLiteral (2001012951256997) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-228122647870862397369) 655360000000000000000),
            (exactRationalLiteral (-25065323132546616153) 102400000000000000000),
            (exactRationalLiteral (517678918081866633) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4575030548411431602137) 4915200000000000000000),
            (exactRationalLiteral (138488552391318072599) 51200000000000000000),
            (exactRationalLiteral (-474640130853948679) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (15756844814092381596523) 9830400000000000000000),
            (exactRationalLiteral (-689165464333557839003) 102400000000000000000),
            (exactRationalLiteral (-6622312188031792949) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10366256248121763344843) 2457600000000000000000),
            (exactRationalLiteral (150618293398469546203) 25600000000000000000),
            (exactRationalLiteral (5397435748756685077) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (109652907686183213403) 40960000000000000000),
            (exactRationalLiteral (-7521141508012216531) 6400000000000000000),
            (exactRationalLiteral (-1516659186001514799) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-3720907015770646951951) 1638400000000000000000),
            (exactRationalLiteral (8330994463444499977) 10240000000000000000),
            (exactRationalLiteral (5257620181269612243) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2838140042818573055377) 819200000000000000000),
            (exactRationalLiteral (-63694163755207841027) 25600000000000000000),
            (exactRationalLiteral (-84162859678593417) 160000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3720907015770646951951) 1638400000000000000000),
            (exactRationalLiteral (8330994463444499977) 10240000000000000000),
            (exactRationalLiteral (5257620181269612243) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (109652907686183213403) 40960000000000000000),
            (exactRationalLiteral (-7521141508012216531) 6400000000000000000),
            (exactRationalLiteral (-1516659186001514799) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-10366256248121763344843) 2457600000000000000000),
            (exactRationalLiteral (150618293398469546203) 25600000000000000000),
            (exactRationalLiteral (5397435748756685077) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (15756844814092381596523) 9830400000000000000000),
            (exactRationalLiteral (-689165464333557839003) 102400000000000000000),
            (exactRationalLiteral (-6622312188031792949) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4575030548411431602137) 4915200000000000000000),
            (exactRationalLiteral (138488552391318072599) 51200000000000000000),
            (exactRationalLiteral (-474640130853948679) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-228122647870862397369) 655360000000000000000),
            (exactRationalLiteral (-25065323132546616153) 102400000000000000000),
            (exactRationalLiteral (517678918081866633) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-31561265919347903707) 491520000000000000000),
            (exactRationalLiteral (-278915239703186809) 25600000000000000000),
            (exactRationalLiteral (2001012951256997) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-102233062698913517203) 4915200000000000000000),
            (exactRationalLiteral (12088879622795571) 51200000000000000000),
            (exactRationalLiteral (5178846256172333) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-22577690365755617337) 3276800000000000000000),
            (exactRationalLiteral (47686416264799999) 20480000000000000000),
            (exactRationalLiteral (4971297511133109) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-48288855916971612019) 9830400000000000000000),
            (exactRationalLiteral (-49032992359485053) 102400000000000000000),
            (exactRationalLiteral (206397691435373) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-28685657911871780849) 3276800000000000000000),
            (exactRationalLiteral (-3060543777785401) 20480000000000000000),
            (exactRationalLiteral (465562369151757) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16815369947167831) 245760000000000000000),
            (exactRationalLiteral (297400848021091) 2560000000000000000),
            (exactRationalLiteral (15120847663573) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2701910758347038761) 2457600000000000000000),
            (exactRationalLiteral (17008769948834191) 25600000000000000000),
            (exactRationalLiteral (180518340999097) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2370616573363541) 1966080000000000000000),
            (exactRationalLiteral (13348785002715769) 102400000000000000000),
            (exactRationalLiteral (-75153735992137) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-759510294462992789) 1638400000000000000000),
            (exactRationalLiteral (-7076250005455121) 51200000000000000000),
            (exactRationalLiteral (153640511484897) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3859035654205252633) 9830400000000000000000),
            (exactRationalLiteral (10835648995363881) 102400000000000000000),
            (exactRationalLiteral (-1800285799148857) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-1880548669296293297) 1966080000000000000000),
            (exactRationalLiteral (-3182142825374291) 4096000000000000000),
            (exactRationalLiteral (7145233064291243) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (959364292028149163) 1228800000000000000000),
            (exactRationalLiteral (9523829280869317) 12800000000000000000),
            (exactRationalLiteral (-4400957414666293) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-115402421334431210659) 9830400000000000000000),
            (exactRationalLiteral (-1292374860745028141) 102400000000000000000),
            (exactRationalLiteral (127214755260595709) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (192009485256357103433) 4915200000000000000000),
            (exactRationalLiteral (4449786421806435767) 51200000000000000000),
            (exactRationalLiteral (-87611524739236279) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1635109236257058289) 131072000000000000000),
            (exactRationalLiteral (-16596177570434952309) 102400000000000000000),
            (exactRationalLiteral (6804476832015237) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-66160815040313665163) 1638400000000000000000),
            (exactRationalLiteral (5635411852553741697) 51200000000000000000),
            (exactRationalLiteral (95488691849583519) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (236581275261165031511) 9830400000000000000000),
            (exactRationalLiteral (-308966767025533819) 20480000000000000000),
            (exactRationalLiteral (-161611335105328777) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12054146998173810341) 9830400000000000000000),
            (exactRationalLiteral (-709067470480812373) 102400000000000000000),
            (exactRationalLiteral (41709851204753669) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (596205520162067151) 409600000000000000000),
          (exactRationalLiteral (30089535434897091887) 1228800000000000000000),
          (exactRationalLiteral (8961838919634325179) 204800000000000000000),
          (exactRationalLiteral (42078641994345089) 2400000000000000000),
          (exactRationalLiteral (6258502916782907) 150000000000000000),
          (exactRationalLiteral (9674753538605999) 800000000000000000),
          (exactRationalLiteral (47572046498977) 60000000000000000),
          (exactRationalLiteral (2348417376585833) 2400000000000000000),
          (exactRationalLiteral (487087889940692209) 1228800000000000000000),
          (exactRationalLiteral (561344118168937) 1200000000000000000),
          (exactRationalLiteral (86852733234883) 16384000000000000000),
          (exactRationalLiteral (448155887917681) 400000000000000000),
          (exactRationalLiteral (3687744671663407) 51200000000000000000),
          (exactRationalLiteral (21020913798621743) 2400000000000000000),
          (exactRationalLiteral (11824990479599879) 2400000000000000000),
          (exactRationalLiteral (8554170635103347299) 1228800000000000000000),
          (exactRationalLiteral (12781752054726362563) 614400000000000000000),
          (exactRationalLiteral (19361860792990051) 300000000000000000),
          (exactRationalLiteral (853371730336199603) 2400000000000000000),
          (exactRationalLiteral (405986621725282257) 400000000000000000),
          (exactRationalLiteral (741777026759095674833) 409600000000000000000),
          (exactRationalLiteral (450052118896240372193) 102400000000000000000),
          (exactRationalLiteral (103917250821795748217) 38400000000000000000),
          (exactRationalLiteral (1408934566412288648429) 614400000000000000000),
          (exactRationalLiteral (1088019728466797736043) 307200000000000000000),
          (exactRationalLiteral (1408934566412288648429) 614400000000000000000),
          (exactRationalLiteral (103917250821795748217) 38400000000000000000),
          (exactRationalLiteral (450052118896240372193) 102400000000000000000),
          (exactRationalLiteral (741777026759095674833) 409600000000000000000),
          (exactRationalLiteral (405986621725282257) 400000000000000000),
          (exactRationalLiteral (853371730336199603) 2400000000000000000),
          (exactRationalLiteral (19361860792990051) 300000000000000000),
          (exactRationalLiteral (12781752054726362563) 614400000000000000000),
          (exactRationalLiteral (8554170635103347299) 1228800000000000000000),
          (exactRationalLiteral (11824990479599879) 2400000000000000000),
          (exactRationalLiteral (21020913798621743) 2400000000000000000),
          (exactRationalLiteral (3687744671663407) 51200000000000000000),
          (exactRationalLiteral (448155887917681) 400000000000000000),
          (exactRationalLiteral (86852733234883) 16384000000000000000),
          (exactRationalLiteral (561344118168937) 1200000000000000000),
          (exactRationalLiteral (487087889940692209) 1228800000000000000000),
          (exactRationalLiteral (2348417376585833) 2400000000000000000),
          (exactRationalLiteral (47572046498977) 60000000000000000),
          (exactRationalLiteral (9674753538605999) 800000000000000000),
          (exactRationalLiteral (6258502916782907) 150000000000000000),
          (exactRationalLiteral (42078641994345089) 2400000000000000000),
          (exactRationalLiteral (8961838919634325179) 204800000000000000000),
          (exactRationalLiteral (30089535434897091887) 1228800000000000000000),
          (exactRationalLiteral (596205520162067151) 409600000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 39),
      (30, 23),
      (30, 7),
      (29, 55),
      (29, 39),
      (29, 23),
      (29, 7),
      (28, 55),
      (28, 39),
      (28, 23),
      (28, 7),
      (27, 55),
      (27, 39),
      (27, 23),
      (27, 7),
      (26, 55),
      (26, 39),
      (26, 23),
      (26, 7),
      (25, 55),
      (25, 39),
      (25, 23),
      (25, 7),
      (24, 55),
      (24, 39),
      (24, 23),
      (24, 7),
      (23, 55),
      (23, 39),
      (23, 23),
      (23, 24),
      (23, 40),
      (23, 56),
      (24, 8),
      (24, 24),
      (24, 40),
      (24, 56),
      (25, 8),
      (25, 24),
      (25, 40),
      (25, 56),
      (26, 8),
      (26, 24),
      (26, 40),
      (26, 56),
      (27, 8),
      (27, 24),
      (27, 40),
      (27, 56),
      (28, 8),
      (28, 24),
      (28, 40),
      (28, 56)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 3
        lower := (exactRationalLiteral (1) 2)
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
            (exactRationalLiteral (22081685931928413) 26214400000000000000),
            (exactRationalLiteral (-22081685931928413) 4096000000000000000),
            (exactRationalLiteral (7360561977309471) 640000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (225490210485577610569) 9830400000000000000000),
            (exactRationalLiteral (-2132642047327714727) 102400000000000000000),
            (exactRationalLiteral (-132292770994694039) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10911250263870724593) 327680000000000000000),
            (exactRationalLiteral (1189008898526682573) 10240000000000000000),
            (exactRationalLiteral (11865525638050413) 320000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-221751049289899315909) 9830400000000000000000),
            (exactRationalLiteral (-16380182098104097973) 102400000000000000000),
            (exactRationalLiteral (101193259333411931) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (72505924842331213373) 1638400000000000000000),
            (exactRationalLiteral (4029794841183869367) 51200000000000000000),
            (exactRationalLiteral (-122384265572046921) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-121513852087822293053) 9830400000000000000000),
            (exactRationalLiteral (-725395165726676333) 102400000000000000000),
            (exactRationalLiteral (31255018449716039) 640000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (960036616115695349) 1228800000000000000000),
            (exactRationalLiteral (-1981916337726591) 2560000000000000000),
            (exactRationalLiteral (-5315748070084843) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-652501046396491621) 655360000000000000000),
            (exactRationalLiteral (-47569499592821851) 102400000000000000000),
            (exactRationalLiteral (8846802456476469) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3817547902328881031) 9830400000000000000000),
            (exactRationalLiteral (2673149545755753) 102400000000000000000),
            (exactRationalLiteral (-2280963925655207) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2318879066476505633) 4915200000000000000000),
            (exactRationalLiteral (-1265774511164637) 10240000000000000000),
            (exactRationalLiteral (220048213331071) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (22410569727159427) 3276800000000000000000),
            (exactRationalLiteral (12995133490700729) 102400000000000000000),
            (exactRationalLiteral (-101672020015383) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2806058815329580583) 2457600000000000000000),
            (exactRationalLiteral (3539090382320867) 5120000000000000000),
            (exactRationalLiteral (6512905615439) 32000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-24955465489729271) 409600000000000000000),
            (exactRationalLiteral (320195291557523) 2560000000000000000),
            (exactRationalLiteral (41865261177507) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-86144625012359011789) 9830400000000000000000),
            (exactRationalLiteral (-113210602658273) 819200000000000000),
            (exactRationalLiteral (110134409169683) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16193059842184681487) 3276800000000000000000),
            (exactRationalLiteral (-47508615455116861) 102400000000000000000),
            (exactRationalLiteral (555790760748723) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-66243529982218648949) 9830400000000000000000),
            (exactRationalLiteral (257963799853835323) 102400000000000000000),
            (exactRationalLiteral (958912350756911) 640000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20419318831144513417) 983040000000000000000),
            (exactRationalLiteral (33698819837539251) 51200000000000000000),
            (exactRationalLiteral (5626123851199507) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-159354188214637409849) 2457600000000000000000),
            (exactRationalLiteral (-236108959055142009) 25600000000000000000),
            (exactRationalLiteral (2279615113547483) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-3565443163847180176201) 9830400000000000000000),
            (exactRationalLiteral (-22706434463192608793) 102400000000000000000),
            (exactRationalLiteral (661765416595137047) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1079559352345729570907) 983040000000000000000),
            (exactRationalLiteral (135355282137679878359) 51200000000000000000),
            (exactRationalLiteral (-1091994995965148441) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3852329769439987118887) 3276800000000000000000),
            (exactRationalLiteral (-708352199843030856027) 102400000000000000000),
            (exactRationalLiteral (-2971055566704715563) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3134373666411643270471) 819200000000000000000),
            (exactRationalLiteral (33907233229792860831) 5120000000000000000),
            (exactRationalLiteral (4061500626490693899) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1582515248893043402423) 614400000000000000000),
            (exactRationalLiteral (-13063581811824936651) 6400000000000000000),
            (exactRationalLiteral (-1254560965904845261) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-10853192350605293160403) 4915200000000000000000),
            (exactRationalLiteral (60939163356339623469) 51200000000000000000),
            (exactRationalLiteral (4384475338288949549) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8127864167078011711853) 2457600000000000000000),
            (exactRationalLiteral (-13009604916330422183) 5120000000000000000),
            (exactRationalLiteral (-256116114829167859) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-10853192350605293160403) 4915200000000000000000),
            (exactRationalLiteral (60939163356339623469) 51200000000000000000),
            (exactRationalLiteral (4384475338288949549) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1582515248893043402423) 614400000000000000000),
            (exactRationalLiteral (-13063581811824936651) 6400000000000000000),
            (exactRationalLiteral (-1254560965904845261) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-3134373666411643270471) 819200000000000000000),
            (exactRationalLiteral (33907233229792860831) 5120000000000000000),
            (exactRationalLiteral (4061500626490693899) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3852329769439987118887) 3276800000000000000000),
            (exactRationalLiteral (-708352199843030856027) 102400000000000000000),
            (exactRationalLiteral (-2971055566704715563) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1079559352345729570907) 983040000000000000000),
            (exactRationalLiteral (135355282137679878359) 51200000000000000000),
            (exactRationalLiteral (-1091994995965148441) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3565443163847180176201) 9830400000000000000000),
            (exactRationalLiteral (-22706434463192608793) 102400000000000000000),
            (exactRationalLiteral (661765416595137047) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-159354188214637409849) 2457600000000000000000),
            (exactRationalLiteral (-236108959055142009) 25600000000000000000),
            (exactRationalLiteral (2279615113547483) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-20419318831144513417) 983040000000000000000),
            (exactRationalLiteral (33698819837539251) 51200000000000000000),
            (exactRationalLiteral (5626123851199507) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-66243529982218648949) 9830400000000000000000),
            (exactRationalLiteral (257963799853835323) 102400000000000000000),
            (exactRationalLiteral (958912350756911) 640000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16193059842184681487) 3276800000000000000000),
            (exactRationalLiteral (-47508615455116861) 102400000000000000000),
            (exactRationalLiteral (555790760748723) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-86144625012359011789) 9830400000000000000000),
            (exactRationalLiteral (-113210602658273) 819200000000000000),
            (exactRationalLiteral (110134409169683) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24955465489729271) 409600000000000000000),
            (exactRationalLiteral (320195291557523) 2560000000000000000),
            (exactRationalLiteral (41865261177507) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2806058815329580583) 2457600000000000000000),
            (exactRationalLiteral (3539090382320867) 5120000000000000000),
            (exactRationalLiteral (6512905615439) 32000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (22410569727159427) 3276800000000000000000),
            (exactRationalLiteral (12995133490700729) 102400000000000000000),
            (exactRationalLiteral (-101672020015383) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2318879066476505633) 4915200000000000000000),
            (exactRationalLiteral (-1265774511164637) 10240000000000000000),
            (exactRationalLiteral (220048213331071) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3817547902328881031) 9830400000000000000000),
            (exactRationalLiteral (2673149545755753) 102400000000000000000),
            (exactRationalLiteral (-2280963925655207) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-652501046396491621) 655360000000000000000),
            (exactRationalLiteral (-47569499592821851) 102400000000000000000),
            (exactRationalLiteral (8846802456476469) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (960036616115695349) 1228800000000000000000),
            (exactRationalLiteral (-1981916337726591) 2560000000000000000),
            (exactRationalLiteral (-5315748070084843) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-121513852087822293053) 9830400000000000000000),
            (exactRationalLiteral (-725395165726676333) 102400000000000000000),
            (exactRationalLiteral (31255018449716039) 640000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (72505924842331213373) 1638400000000000000000),
            (exactRationalLiteral (4029794841183869367) 51200000000000000000),
            (exactRationalLiteral (-122384265572046921) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-221751049289899315909) 9830400000000000000000),
            (exactRationalLiteral (-16380182098104097973) 102400000000000000000),
            (exactRationalLiteral (101193259333411931) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10911250263870724593) 327680000000000000000),
            (exactRationalLiteral (1189008898526682573) 10240000000000000000),
            (exactRationalLiteral (11865525638050413) 320000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (225490210485577610569) 9830400000000000000000),
            (exactRationalLiteral (-2132642047327714727) 102400000000000000000),
            (exactRationalLiteral (-132292770994694039) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22081685931928413) 26214400000000000000),
            (exactRationalLiteral (-22081685931928413) 4096000000000000000),
            (exactRationalLiteral (7360561977309471) 640000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (2453520659103157) 2400000000000000000),
          (exactRationalLiteral (18837613853558053) 800000000000000000),
          (exactRationalLiteral (7377434245587593) 200000000000000000),
          (exactRationalLiteral (11272534225623361487) 409600000000000000000),
          (exactRationalLiteral (28652827485426587767) 614400000000000000000),
          (exactRationalLiteral (15400835267470323653) 1228800000000000000000),
          (exactRationalLiteral (634638379262177) 800000000000000000),
          (exactRationalLiteral (1237854125332539731) 1228800000000000000000),
          (exactRationalLiteral (311862785130197) 800000000000000000),
          (exactRationalLiteral (97382180652210787) 204800000000000000000),
          (exactRationalLiteral (13237354306440337) 1228800000000000000000),
          (exactRationalLiteral (357453098891905619) 307200000000000000000),
          (exactRationalLiteral (77692482681421) 1200000000000000000),
          (exactRationalLiteral (3591121929129514423) 409600000000000000000),
          (exactRationalLiteral (243599316520512461) 49152000000000000000),
          (exactRationalLiteral (16358141925937531) 2400000000000000000),
          (exactRationalLiteral (4157756993915979) 200000000000000000),
          (exactRationalLiteral (20003453044961737177) 307200000000000000000),
          (exactRationalLiteral (151312713655738164843) 409600000000000000000),
          (exactRationalLiteral (725034743215154555551) 614400000000000000000),
          (exactRationalLiteral (667544292619056457) 480000000000000000),
          (exactRationalLiteral (2416718024472953527) 600000000000000000),
          (exactRationalLiteral (3159787621720225277) 1200000000000000000),
          (exactRationalLiteral (168188779331023481) 75000000000000000),
          (exactRationalLiteral (2031776743990893223) 600000000000000000),
          (exactRationalLiteral (168188779331023481) 75000000000000000),
          (exactRationalLiteral (3159787621720225277) 1200000000000000000),
          (exactRationalLiteral (2416718024472953527) 600000000000000000),
          (exactRationalLiteral (667544292619056457) 480000000000000000),
          (exactRationalLiteral (725034743215154555551) 614400000000000000000),
          (exactRationalLiteral (151312713655738164843) 409600000000000000000),
          (exactRationalLiteral (20003453044961737177) 307200000000000000000),
          (exactRationalLiteral (4157756993915979) 200000000000000000),
          (exactRationalLiteral (16358141925937531) 2400000000000000000),
          (exactRationalLiteral (243599316520512461) 49152000000000000000),
          (exactRationalLiteral (3591121929129514423) 409600000000000000000),
          (exactRationalLiteral (77692482681421) 1200000000000000000),
          (exactRationalLiteral (357453098891905619) 307200000000000000000),
          (exactRationalLiteral (13237354306440337) 1228800000000000000000),
          (exactRationalLiteral (97382180652210787) 204800000000000000000),
          (exactRationalLiteral (311862785130197) 800000000000000000),
          (exactRationalLiteral (1237854125332539731) 1228800000000000000000),
          (exactRationalLiteral (634638379262177) 800000000000000000),
          (exactRationalLiteral (15400835267470323653) 1228800000000000000000),
          (exactRationalLiteral (28652827485426587767) 614400000000000000000),
          (exactRationalLiteral (11272534225623361487) 409600000000000000000),
          (exactRationalLiteral (7377434245587593) 200000000000000000),
          (exactRationalLiteral (18837613853558053) 800000000000000000),
          (exactRationalLiteral (2453520659103157) 2400000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 40),
      (30, 24),
      (30, 8),
      (29, 56),
      (29, 40),
      (29, 24),
      (29, 8),
      (28, 56),
      (28, 40),
      (28, 24),
      (28, 8),
      (27, 56),
      (27, 40),
      (27, 24),
      (27, 8),
      (26, 56),
      (26, 40),
      (26, 24),
      (26, 8),
      (25, 56),
      (25, 40),
      (25, 24),
      (25, 8),
      (24, 56),
      (24, 40),
      (24, 24),
      (24, 8),
      (23, 56),
      (23, 40),
      (23, 24),
      (23, 23),
      (23, 39),
      (23, 55),
      (24, 7),
      (24, 23),
      (24, 39),
      (24, 55),
      (25, 7),
      (25, 23),
      (25, 39),
      (25, 55),
      (26, 7),
      (26, 23),
      (26, 39),
      (26, 55),
      (27, 7),
      (27, 23),
      (27, 39),
      (27, 55),
      (28, 7),
      (28, 23),
      (28, 39),
      (28, 55)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 3
        lower := (exactRationalLiteral (9) 16)
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
            (exactRationalLiteral (5390384888049635929) 9830400000000000000000),
            (exactRationalLiteral (-414644991388433533) 102400000000000000000),
            (exactRationalLiteral (31895768568341041) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (70408039735372510897) 3276800000000000000000),
            (exactRationalLiteral (-2603176003085221407) 102400000000000000000),
            (exactRationalLiteral (-102974206884059301) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-42477066572871564247) 1638400000000000000000),
            (exactRationalLiteral (6110032878075758217) 51200000000000000000),
            (exactRationalLiteral (23166564530920611) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-318440267636517373799) 9830400000000000000000),
            (exactRationalLiteral (-15786631495767656861) 102400000000000000000),
            (exactRationalLiteral (1564656334678469) 25600000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (240088841423901050701) 4915200000000000000000),
            (exactRationalLiteral (3470712297230060399) 51200000000000000000),
            (exactRationalLiteral (-157157006404857563) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-41291560209082483589) 3276800000000000000000),
            (exactRationalLiteral (-42174122756386581) 102400000000000000000),
            (exactRationalLiteral (185335429236564681) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (833130986521205303) 1228800000000000000000),
            (exactRationalLiteral (-33002155279809427) 12800000000000000000),
            (exactRationalLiteral (-6230538725503393) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-9959964786457846889) 9830400000000000000000),
            (exactRationalLiteral (-8779150982545523) 102400000000000000000),
            (exactRationalLiteral (2109674369732339) 640000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1276934428222744799) 3276800000000000000000),
            (exactRationalLiteral (-296482496395111) 4096000000000000000),
            (exactRationalLiteral (-2761642052161557) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-470789218488817439) 983040000000000000000),
            (exactRationalLiteral (-5315864298806553) 51200000000000000000),
            (exactRationalLiteral (57291183035449) 320000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5755054909976203) 393216000000000000000),
            (exactRationalLiteral (2507081768518541) 20480000000000000000),
            (exactRationalLiteral (-128190304038629) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (194274307712092387) 163840000000000000000),
            (exactRationalLiteral (18311351071921991) 25600000000000000000),
            (exactRationalLiteral (145126939772853) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-64651176934276303) 1228800000000000000000),
            (exactRationalLiteral (1821926329525511) 12800000000000000000),
            (exactRationalLiteral (68609674691441) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-86229633063282608639) 9830400000000000000000),
            (exactRationalLiteral (-14421643615569541) 102400000000000000000),
            (exactRationalLiteral (-245293550812391) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-48856164157878507551) 9830400000000000000000),
            (exactRationalLiteral (-44586666273495269) 102400000000000000000),
            (exactRationalLiteral (905183830062073) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-64638919385079616567) 9830400000000000000000),
            (exactRationalLiteral (55357715070855287) 20480000000000000000),
            (exactRationalLiteral (4617825996436001) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-33941699546700942933) 1638400000000000000000),
            (exactRationalLiteral (57097870432391627) 51200000000000000000),
            (exactRationalLiteral (6073401446226681) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-160628493018909603203) 2457600000000000000000),
            (exactRationalLiteral (-187730635161287489) 25600000000000000000),
            (exactRationalLiteral (2558217275837969) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-3693164239633141102739) 9830400000000000000000),
            (exactRationalLiteral (-19771199799785519777) 102400000000000000000),
            (exactRationalLiteral (805851915108407461) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2064785031714233514783) 1638400000000000000000),
            (exactRationalLiteral (129752592423596885071) 51200000000000000000),
            (exactRationalLiteral (-1709349861076348203) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7285828468946627943287) 9830400000000000000000),
            (exactRationalLiteral (-712933908867195563507) 102400000000000000000),
            (exactRationalLiteral (680201054622361823) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8342509735312319624407) 2457600000000000000000),
            (exactRationalLiteral (36622059682079019479) 5120000000000000000),
            (exactRationalLiteral (2725565504224702721) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1490127419311622317537) 614400000000000000000),
            (exactRationalLiteral (-17557629235250978619) 6400000000000000000),
            (exactRationalLiteral (-992462745808175723) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-10438436245779710675777) 4915200000000000000000),
            (exactRationalLiteral (76730775023534096277) 51200000000000000000),
            (exactRationalLiteral (702266099061657371) 320000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7735161418944404228959) 2457600000000000000000),
            (exactRationalLiteral (-65743092673841183899) 25600000000000000000),
            (exactRationalLiteral (-91417931265368633) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-10438436245779710675777) 4915200000000000000000),
            (exactRationalLiteral (76730775023534096277) 51200000000000000000),
            (exactRationalLiteral (702266099061657371) 320000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1490127419311622317537) 614400000000000000000),
            (exactRationalLiteral (-17557629235250978619) 6400000000000000000),
            (exactRationalLiteral (-992462745808175723) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-8342509735312319624407) 2457600000000000000000),
            (exactRationalLiteral (36622059682079019479) 5120000000000000000),
            (exactRationalLiteral (2725565504224702721) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (7285828468946627943287) 9830400000000000000000),
            (exactRationalLiteral (-712933908867195563507) 102400000000000000000),
            (exactRationalLiteral (680201054622361823) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2064785031714233514783) 1638400000000000000000),
            (exactRationalLiteral (129752592423596885071) 51200000000000000000),
            (exactRationalLiteral (-1709349861076348203) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3693164239633141102739) 9830400000000000000000),
            (exactRationalLiteral (-19771199799785519777) 102400000000000000000),
            (exactRationalLiteral (805851915108407461) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-160628493018909603203) 2457600000000000000000),
            (exactRationalLiteral (-187730635161287489) 25600000000000000000),
            (exactRationalLiteral (2558217275837969) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-33941699546700942933) 1638400000000000000000),
            (exactRationalLiteral (57097870432391627) 51200000000000000000),
            (exactRationalLiteral (6073401446226681) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-64638919385079616567) 9830400000000000000000),
            (exactRationalLiteral (55357715070855287) 20480000000000000000),
            (exactRationalLiteral (4617825996436001) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-48856164157878507551) 9830400000000000000000),
            (exactRationalLiteral (-44586666273495269) 102400000000000000000),
            (exactRationalLiteral (905183830062073) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-86229633063282608639) 9830400000000000000000),
            (exactRationalLiteral (-14421643615569541) 102400000000000000000),
            (exactRationalLiteral (-245293550812391) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-64651176934276303) 1228800000000000000000),
            (exactRationalLiteral (1821926329525511) 12800000000000000000),
            (exactRationalLiteral (68609674691441) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (194274307712092387) 163840000000000000000),
            (exactRationalLiteral (18311351071921991) 25600000000000000000),
            (exactRationalLiteral (145126939772853) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (5755054909976203) 393216000000000000000),
            (exactRationalLiteral (2507081768518541) 20480000000000000000),
            (exactRationalLiteral (-128190304038629) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-470789218488817439) 983040000000000000000),
            (exactRationalLiteral (-5315864298806553) 51200000000000000000),
            (exactRationalLiteral (57291183035449) 320000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1276934428222744799) 3276800000000000000000),
            (exactRationalLiteral (-296482496395111) 4096000000000000000),
            (exactRationalLiteral (-2761642052161557) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-9959964786457846889) 9830400000000000000000),
            (exactRationalLiteral (-8779150982545523) 102400000000000000000),
            (exactRationalLiteral (2109674369732339) 640000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (833130986521205303) 1228800000000000000000),
            (exactRationalLiteral (-33002155279809427) 12800000000000000000),
            (exactRationalLiteral (-6230538725503393) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-41291560209082483589) 3276800000000000000000),
            (exactRationalLiteral (-42174122756386581) 102400000000000000000),
            (exactRationalLiteral (185335429236564681) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (240088841423901050701) 4915200000000000000000),
            (exactRationalLiteral (3470712297230060399) 51200000000000000000),
            (exactRationalLiteral (-157157006404857563) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-318440267636517373799) 9830400000000000000000),
            (exactRationalLiteral (-15786631495767656861) 102400000000000000000),
            (exactRationalLiteral (1564656334678469) 25600000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-42477066572871564247) 1638400000000000000000),
            (exactRationalLiteral (6110032878075758217) 51200000000000000000),
            (exactRationalLiteral (23166564530920611) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (70408039735372510897) 3276800000000000000000),
            (exactRationalLiteral (-2603176003085221407) 102400000000000000000),
            (exactRationalLiteral (-102974206884059301) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5390384888049635929) 9830400000000000000000),
            (exactRationalLiteral (-414644991388433533) 102400000000000000000),
            (exactRationalLiteral (31895768568341041) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (841557586072382851) 1228800000000000000000),
          (exactRationalLiteral (5467751632816642541) 245760000000000000000),
          (exactRationalLiteral (6069738255309147493) 204800000000000000000),
          (exactRationalLiteral (1141144442522078813) 30720000000000000000),
          (exactRationalLiteral (1302146463156042989) 25600000000000000000),
          (exactRationalLiteral (3878647510866699821) 307200000000000000000),
          (exactRationalLiteral (22847580787795817) 30720000000000000000),
          (exactRationalLiteral (62375894337407167) 61440000000000000000),
          (exactRationalLiteral (60336949017462587) 153600000000000000000),
          (exactRationalLiteral (37015642402250813) 76800000000000000000),
          (exactRationalLiteral (188629967940683) 10240000000000000000),
          (exactRationalLiteral (46398050029158809) 38400000000000000000),
          (exactRationalLiteral (1748112477638387) 30720000000000000000),
          (exactRationalLiteral (1348028306074402273) 153600000000000000000),
          (exactRationalLiteral (255140801607677867) 51200000000000000000),
          (exactRationalLiteral (2727305969386435983) 409600000000000000000),
          (exactRationalLiteral (12747299460732354653) 614400000000000000000),
          (exactRationalLiteral (503601922374531781) 7680000000000000000),
          (exactRationalLiteral (11718713250118486889) 30720000000000000000),
          (exactRationalLiteral (102784002271839164923) 76800000000000000000),
          (exactRationalLiteral (1178105646300177272573) 1228800000000000000000),
          (exactRationalLiteral (222074899161742445321) 61440000000000000000),
          (exactRationalLiteral (16038456975728149911) 6400000000000000000),
          (exactRationalLiteral (444069083622620740529) 204800000000000000000),
          (exactRationalLiteral (330501420586681240631) 102400000000000000000),
          (exactRationalLiteral (444069083622620740529) 204800000000000000000),
          (exactRationalLiteral (16038456975728149911) 6400000000000000000),
          (exactRationalLiteral (222074899161742445321) 61440000000000000000),
          (exactRationalLiteral (1178105646300177272573) 1228800000000000000000),
          (exactRationalLiteral (102784002271839164923) 76800000000000000000),
          (exactRationalLiteral (11718713250118486889) 30720000000000000000),
          (exactRationalLiteral (503601922374531781) 7680000000000000000),
          (exactRationalLiteral (12747299460732354653) 614400000000000000000),
          (exactRationalLiteral (2727305969386435983) 409600000000000000000),
          (exactRationalLiteral (255140801607677867) 51200000000000000000),
          (exactRationalLiteral (1348028306074402273) 153600000000000000000),
          (exactRationalLiteral (1748112477638387) 30720000000000000000),
          (exactRationalLiteral (46398050029158809) 38400000000000000000),
          (exactRationalLiteral (188629967940683) 10240000000000000000),
          (exactRationalLiteral (37015642402250813) 76800000000000000000),
          (exactRationalLiteral (60336949017462587) 153600000000000000000),
          (exactRationalLiteral (62375894337407167) 61440000000000000000),
          (exactRationalLiteral (22847580787795817) 30720000000000000000),
          (exactRationalLiteral (3878647510866699821) 307200000000000000000),
          (exactRationalLiteral (1302146463156042989) 25600000000000000000),
          (exactRationalLiteral (1141144442522078813) 30720000000000000000),
          (exactRationalLiteral (6069738255309147493) 204800000000000000000),
          (exactRationalLiteral (5467751632816642541) 245760000000000000000),
          (exactRationalLiteral (841557586072382851) 1228800000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 41),
      (30, 25),
      (30, 9),
      (29, 57),
      (29, 41),
      (29, 25),
      (29, 9),
      (28, 57),
      (28, 41),
      (28, 25),
      (28, 9),
      (27, 57),
      (27, 41),
      (27, 25),
      (27, 9),
      (26, 57),
      (26, 41),
      (26, 25),
      (26, 9),
      (25, 57),
      (25, 41),
      (25, 25),
      (25, 9),
      (24, 57),
      (24, 41),
      (24, 25),
      (24, 9),
      (23, 57),
      (23, 41),
      (23, 25),
      (23, 22),
      (23, 38),
      (23, 54),
      (24, 6),
      (24, 22),
      (24, 38),
      (24, 54),
      (25, 6),
      (25, 22),
      (25, 38),
      (25, 54),
      (26, 6),
      (26, 22),
      (26, 38),
      (26, 54),
      (27, 6),
      (27, 22),
      (27, 38),
      (27, 54),
      (28, 6),
      (28, 22),
      (28, 38),
      (28, 54)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 3
        lower := (exactRationalLiteral (5) 8)
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
            (exactRationalLiteral (3265635997266301967) 9830400000000000000000),
            (exactRationalLiteral (-296875999751481997) 102400000000000000000),
            (exactRationalLiteral (26988727250134727) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (194486646961440031589) 9830400000000000000000),
            (exactRationalLiteral (-591287140480037827) 20480000000000000000),
            (exactRationalLiteral (-73655642773424563) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-30212549310142140641) 1638400000000000000000),
            (exactRationalLiteral (6130377008880777753) 51200000000000000000),
            (exactRationalLiteral (-12994499128410843) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-136811838993033341563) 3276800000000000000000),
            (exactRationalLiteral (-14815525763425628973) 102400000000000000000),
            (exactRationalLiteral (289970824336205319) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (258888140167091879771) 4915200000000000000000),
            (exactRationalLiteral (2772538789945008863) 51200000000000000000),
            (exactRationalLiteral (-38385949447533641) 320000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-121787458864995056137) 9830400000000000000000),
            (exactRationalLiteral (151457653633168223) 20480000000000000000),
            (exactRationalLiteral (214395766224549167) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22267697100585353) 49152000000000000000),
            (exactRationalLiteral (-59753891492660099) 12800000000000000000),
            (exactRationalLiteral (-7145329380921943) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-9879252952600438783) 9830400000000000000000),
            (exactRationalLiteral (36817475196471709) 102400000000000000000),
            (exactRationalLiteral (12249941240846921) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3910338076259465131) 9830400000000000000000),
            (exactRationalLiteral (-19419986871536703) 102400000000000000000),
            (exactRationalLiteral (-3242320178667907) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-794046058815804959) 1638400000000000000000),
            (exactRationalLiteral (-161489009376209) 2048000000000000000),
            (exactRationalLiteral (352863617023419) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (217444469020404773) 9830400000000000000000),
            (exactRationalLiteral (11969611058391697) 102400000000000000000),
            (exactRationalLiteral (-247533740899) 5120000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3025653462587739499) 2457600000000000000000),
            (exactRationalLiteral (18856467429787159) 25600000000000000000),
            (exactRationalLiteral (127431239159731) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-52789325206770209) 1228800000000000000000),
            (exactRationalLiteral (2149853855319143) 12800000000000000000),
            (exactRationalLiteral (762832705643) 3200000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-28773509386475234291) 3276800000000000000000),
            (exactRationalLiteral (-16113673738783253) 102400000000000000000),
            (exactRationalLiteral (-120144302158893) 640000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49111424377281480889) 9830400000000000000000),
            (exactRationalLiteral (-40267144814620277) 102400000000000000000),
            (exactRationalLiteral (1254576899375423) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-20974493654675373387) 3276800000000000000000),
            (exactRationalLiteral (294906407825323331) 102400000000000000000),
            (exactRationalLiteral (4441090239087447) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-101407841489773650169) 4915200000000000000000),
            (exactRationalLiteral (82286031407352699) 51200000000000000000),
            (exactRationalLiteral (1304135808250771) 320000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-161595811750081240277) 2457600000000000000000),
            (exactRationalLiteral (-133780268021623249) 25600000000000000000),
            (exactRationalLiteral (567363887625691) 32000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-1267181623152166750071) 3276800000000000000000),
            (exactRationalLiteral (-3251923828465069821) 20480000000000000000),
            (exactRationalLiteral (7599507308973423) 25600000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6949889031890920877291) 4915200000000000000000),
            (exactRationalLiteral (24336096649813818547) 10240000000000000000),
            (exactRationalLiteral (-465340945237509593) 320000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (606198490976846242733) 1966080000000000000000),
            (exactRationalLiteral (-702910591406051961443) 102400000000000000000),
            (exactRationalLiteral (4331457675949439209) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7216484899288316572097) 2457600000000000000000),
            (exactRationalLiteral (191340690182761925923) 25600000000000000000),
            (exactRationalLiteral (1389630381958711543) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (457973494610268338433) 204800000000000000000),
            (exactRationalLiteral (-4200656755658068487) 1280000000000000000),
            (exactRationalLiteral (-146072905142301237) 40000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-3313136069688909768877) 1638400000000000000000),
            (exactRationalLiteral (89029807318805918309) 51200000000000000000),
            (exactRationalLiteral (2638185652327624161) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2446754880153475966291) 819200000000000000000),
            (exactRationalLiteral (-65779368031775059979) 25600000000000000000),
            (exactRationalLiteral (73280252298430593) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3313136069688909768877) 1638400000000000000000),
            (exactRationalLiteral (89029807318805918309) 51200000000000000000),
            (exactRationalLiteral (2638185652327624161) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (457973494610268338433) 204800000000000000000),
            (exactRationalLiteral (-4200656755658068487) 1280000000000000000),
            (exactRationalLiteral (-146072905142301237) 40000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-7216484899288316572097) 2457600000000000000000),
            (exactRationalLiteral (191340690182761925923) 25600000000000000000),
            (exactRationalLiteral (1389630381958711543) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (606198490976846242733) 1966080000000000000000),
            (exactRationalLiteral (-702910591406051961443) 102400000000000000000),
            (exactRationalLiteral (4331457675949439209) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6949889031890920877291) 4915200000000000000000),
            (exactRationalLiteral (24336096649813818547) 10240000000000000000),
            (exactRationalLiteral (-465340945237509593) 320000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1267181623152166750071) 3276800000000000000000),
            (exactRationalLiteral (-3251923828465069821) 20480000000000000000),
            (exactRationalLiteral (7599507308973423) 25600000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-161595811750081240277) 2457600000000000000000),
            (exactRationalLiteral (-133780268021623249) 25600000000000000000),
            (exactRationalLiteral (567363887625691) 32000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-101407841489773650169) 4915200000000000000000),
            (exactRationalLiteral (82286031407352699) 51200000000000000000),
            (exactRationalLiteral (1304135808250771) 320000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20974493654675373387) 3276800000000000000000),
            (exactRationalLiteral (294906407825323331) 102400000000000000000),
            (exactRationalLiteral (4441090239087447) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49111424377281480889) 9830400000000000000000),
            (exactRationalLiteral (-40267144814620277) 102400000000000000000),
            (exactRationalLiteral (1254576899375423) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-28773509386475234291) 3276800000000000000000),
            (exactRationalLiteral (-16113673738783253) 102400000000000000000),
            (exactRationalLiteral (-120144302158893) 640000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-52789325206770209) 1228800000000000000000),
            (exactRationalLiteral (2149853855319143) 12800000000000000000),
            (exactRationalLiteral (762832705643) 3200000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (3025653462587739499) 2457600000000000000000),
            (exactRationalLiteral (18856467429787159) 25600000000000000000),
            (exactRationalLiteral (127431239159731) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (217444469020404773) 9830400000000000000000),
            (exactRationalLiteral (11969611058391697) 102400000000000000000),
            (exactRationalLiteral (-247533740899) 5120000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-794046058815804959) 1638400000000000000000),
            (exactRationalLiteral (-161489009376209) 2048000000000000000),
            (exactRationalLiteral (352863617023419) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3910338076259465131) 9830400000000000000000),
            (exactRationalLiteral (-19419986871536703) 102400000000000000000),
            (exactRationalLiteral (-3242320178667907) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-9879252952600438783) 9830400000000000000000),
            (exactRationalLiteral (36817475196471709) 102400000000000000000),
            (exactRationalLiteral (12249941240846921) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22267697100585353) 49152000000000000000),
            (exactRationalLiteral (-59753891492660099) 12800000000000000000),
            (exactRationalLiteral (-7145329380921943) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-121787458864995056137) 9830400000000000000000),
            (exactRationalLiteral (151457653633168223) 20480000000000000000),
            (exactRationalLiteral (214395766224549167) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (258888140167091879771) 4915200000000000000000),
            (exactRationalLiteral (2772538789945008863) 51200000000000000000),
            (exactRationalLiteral (-38385949447533641) 320000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-136811838993033341563) 3276800000000000000000),
            (exactRationalLiteral (-14815525763425628973) 102400000000000000000),
            (exactRationalLiteral (289970824336205319) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-30212549310142140641) 1638400000000000000000),
            (exactRationalLiteral (6130377008880777753) 51200000000000000000),
            (exactRationalLiteral (-12994499128410843) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (194486646961440031589) 9830400000000000000000),
            (exactRationalLiteral (-591287140480037827) 20480000000000000000),
            (exactRationalLiteral (-73655642773424563) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3265635997266301967) 9830400000000000000000),
            (exactRationalLiteral (-296875999751481997) 102400000000000000000),
            (exactRationalLiteral (26988727250134727) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (22081685931928413) 51200000000000000000),
          (exactRationalLiteral (3173755122785390749) 153600000000000000000),
          (exactRationalLiteral (567967093347001677) 25600000000000000000),
          (exactRationalLiteral (56745623425639699663) 1228800000000000000000),
          (exactRationalLiteral (33326572615599687053) 614400000000000000000),
          (exactRationalLiteral (1928604164676764441) 153600000000000000000),
          (exactRationalLiteral (11171492330899337) 19200000000000000000),
          (exactRationalLiteral (10368548269961881) 10240000000000000000),
          (exactRationalLiteral (165773555686388839) 409600000000000000000),
          (exactRationalLiteral (299144757181079651) 614400000000000000000),
          (exactRationalLiteral (31609489661172827) 1228800000000000000000),
          (exactRationalLiteral (128441512947678067) 102400000000000000000),
          (exactRationalLiteral (15355780394497) 320000000000000000),
          (exactRationalLiteral (10796356132394303383) 1228800000000000000000),
          (exactRationalLiteral (6153535923061569847) 1228800000000000000000),
          (exactRationalLiteral (996793571076658649) 153600000000000000000),
          (exactRationalLiteral (1588052518526085317) 76800000000000000000),
          (exactRationalLiteral (20244237969646057123) 307200000000000000000),
          (exactRationalLiteral (480925233549169328587) 1228800000000000000000),
          (exactRationalLiteral (60897014083558415931) 40960000000000000000),
          (exactRationalLiteral (26827567571976936859) 51200000000000000000),
          (exactRationalLiteral (40550365162133298019) 12800000000000000000),
          (exactRationalLiteral (8966301202990582433) 3840000000000000000),
          (exactRationalLiteral (159346039088198029027) 76800000000000000000),
          (exactRationalLiteral (117777191190951038609) 38400000000000000000),
          (exactRationalLiteral (159346039088198029027) 76800000000000000000),
          (exactRationalLiteral (8966301202990582433) 3840000000000000000),
          (exactRationalLiteral (40550365162133298019) 12800000000000000000),
          (exactRationalLiteral (26827567571976936859) 51200000000000000000),
          (exactRationalLiteral (60897014083558415931) 40960000000000000000),
          (exactRationalLiteral (480925233549169328587) 1228800000000000000000),
          (exactRationalLiteral (20244237969646057123) 307200000000000000000),
          (exactRationalLiteral (1588052518526085317) 76800000000000000000),
          (exactRationalLiteral (996793571076658649) 153600000000000000000),
          (exactRationalLiteral (6153535923061569847) 1228800000000000000000),
          (exactRationalLiteral (10796356132394303383) 1228800000000000000000),
          (exactRationalLiteral (15355780394497) 320000000000000000),
          (exactRationalLiteral (128441512947678067) 102400000000000000000),
          (exactRationalLiteral (31609489661172827) 1228800000000000000000),
          (exactRationalLiteral (299144757181079651) 614400000000000000000),
          (exactRationalLiteral (165773555686388839) 409600000000000000000),
          (exactRationalLiteral (10368548269961881) 10240000000000000000),
          (exactRationalLiteral (11171492330899337) 19200000000000000000),
          (exactRationalLiteral (1928604164676764441) 153600000000000000000),
          (exactRationalLiteral (33326572615599687053) 614400000000000000000),
          (exactRationalLiteral (56745623425639699663) 1228800000000000000000),
          (exactRationalLiteral (567967093347001677) 25600000000000000000),
          (exactRationalLiteral (3173755122785390749) 153600000000000000000),
          (exactRationalLiteral (22081685931928413) 51200000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 42),
      (30, 26),
      (30, 10),
      (29, 58),
      (29, 42),
      (29, 26),
      (29, 10),
      (28, 58),
      (28, 42),
      (28, 26),
      (28, 10),
      (27, 58),
      (27, 42),
      (27, 26),
      (27, 10),
      (26, 58),
      (26, 42),
      (26, 26),
      (26, 10),
      (25, 58),
      (25, 42),
      (25, 26),
      (25, 10),
      (24, 58),
      (24, 42),
      (24, 26),
      (24, 10),
      (23, 58),
      (23, 42),
      (23, 26),
      (23, 21),
      (23, 37),
      (23, 53),
      (24, 5),
      (24, 21),
      (24, 37),
      (24, 53),
      (25, 5),
      (25, 21),
      (25, 37),
      (25, 53),
      (26, 5),
      (26, 21),
      (26, 37),
      (26, 53),
      (27, 5),
      (27, 21),
      (27, 37),
      (27, 53),
      (28, 5),
      (28, 21),
      (28, 37),
      (28, 53)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 3
        lower := (exactRationalLiteral (11) 16)
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
            (exactRationalLiteral (596205520162067151) 3276800000000000000000),
            (exactRationalLiteral (-198735173387355717) 102400000000000000000),
            (exactRationalLiteral (22081685931928413) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7039257571608013639) 393216000000000000000),
            (exactRationalLiteral (-3192421145272617911) 102400000000000000000),
            (exactRationalLiteral (-1773483146511593) 128000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18051988040440003779) 1638400000000000000000),
            (exactRationalLiteral (6006076885048471473) 51200000000000000000),
            (exactRationalLiteral (-49155562787742297) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-495471466537613747923) 9830400000000000000000),
            (exactRationalLiteral (-13466864901078014309) 102400000000000000000),
            (exactRationalLiteral (384359606837602013) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (91027041658859557307) 1638400000000000000000),
            (exactRationalLiteral (1935274319328714759) 51200000000000000000),
            (exactRationalLiteral (-226702488070478847) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-114554738713353481499) 9830400000000000000000),
            (exactRationalLiteral (334598401408001351) 20480000000000000000),
            (exactRationalLiteral (243456103212533653) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (21753192673187143) 245760000000000000000),
            (exactRationalLiteral (-90164790327184971) 12800000000000000000),
            (exactRationalLiteral (-8060120036340493) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-3168180842987568191) 3276800000000000000000),
            (exactRationalLiteral (17844075788845969) 20480000000000000000),
            (exactRationalLiteral (13951510633032147) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4067688552138725633) 9830400000000000000000),
            (exactRationalLiteral (-33350623839221031) 102400000000000000000),
            (exactRationalLiteral (-3722998305174257) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2401861533642180503) 4915200000000000000000),
            (exactRationalLiteral (-2492955362619201) 51200000000000000000),
            (exactRationalLiteral (419271318869593) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (95766519725973157) 3276800000000000000000),
            (exactRationalLiteral (2259548027619541) 20480000000000000000),
            (exactRationalLiteral (-181226872085121) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3140250659233926737) 2457600000000000000000),
            (exactRationalLiteral (19330800985199839) 25600000000000000000),
            (exactRationalLiteral (109735538546609) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2575931690822341) 81920000000000000000),
            (exactRationalLiteral (2584759035168511) 12800000000000000000),
            (exactRationalLiteral (122098501719309) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-86425840571827864267) 9830400000000000000000),
            (exactRationalLiteral (-19227415701925261) 102400000000000000000),
            (exactRationalLiteral (-956149470776539) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-657820996681325921) 131072000000000000000),
            (exactRationalLiteral (-6910010215698377) 20480000000000000000),
            (exactRationalLiteral (1603969968688773) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-61101456377234525027) 9830400000000000000000),
            (exactRationalLiteral (312317297266976011) 102400000000000000000),
            (exactRationalLiteral (4264354481738893) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-100834088042454379019) 4915200000000000000000),
            (exactRationalLiteral (109263302762422467) 51200000000000000000),
            (exactRationalLiteral (6967956636281029) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-162222712148677462751) 2457600000000000000000),
            (exactRationalLiteral (-74257857636149289) 25600000000000000000),
            (exactRationalLiteral (3115421600418941) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-3887126977352939128687) 9830400000000000000000),
            (exactRationalLiteral (-12171692490812096777) 102400000000000000000),
            (exactRationalLiteral (1094024912134948289) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7649582055210640059073) 4915200000000000000000),
            (exactRationalLiteral (111138954614096501351) 51200000000000000000),
            (exactRationalLiteral (-2944059591298747727) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-373296191651792991647) 3276800000000000000000),
            (exactRationalLiteral (-135656449491920009967) 20480000000000000000),
            (exactRationalLiteral (1596542859455303319) 640000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-403807262273153629517) 163840000000000000000),
            (exactRationalLiteral (194227341466064789739) 25600000000000000000),
            (exactRationalLiteral (10739051938544073) 160000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1240184799732911564621) 614400000000000000000),
            (exactRationalLiteral (-23400545440943028099) 6400000000000000000),
            (exactRationalLiteral (-468266305614836647) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-9377063716697884957621) 4915200000000000000000),
            (exactRationalLiteral (19567252048431017913) 10240000000000000000),
            (exactRationalLiteral (1765040809346961467) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6947126588031613903019) 2457600000000000000000),
            (exactRationalLiteral (-13031370131090747831) 5120000000000000000),
            (exactRationalLiteral (237978435862229819) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-9377063716697884957621) 4915200000000000000000),
            (exactRationalLiteral (19567252048431017913) 10240000000000000000),
            (exactRationalLiteral (1765040809346961467) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1240184799732911564621) 614400000000000000000),
            (exactRationalLiteral (-23400545440943028099) 6400000000000000000),
            (exactRationalLiteral (-468266305614836647) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-403807262273153629517) 163840000000000000000),
            (exactRationalLiteral (194227341466064789739) 25600000000000000000),
            (exactRationalLiteral (10739051938544073) 160000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-373296191651792991647) 3276800000000000000000),
            (exactRationalLiteral (-135656449491920009967) 20480000000000000000),
            (exactRationalLiteral (1596542859455303319) 640000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7649582055210640059073) 4915200000000000000000),
            (exactRationalLiteral (111138954614096501351) 51200000000000000000),
            (exactRationalLiteral (-2944059591298747727) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3887126977352939128687) 9830400000000000000000),
            (exactRationalLiteral (-12171692490812096777) 102400000000000000000),
            (exactRationalLiteral (1094024912134948289) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-162222712148677462751) 2457600000000000000000),
            (exactRationalLiteral (-74257857636149289) 25600000000000000000),
            (exactRationalLiteral (3115421600418941) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-100834088042454379019) 4915200000000000000000),
            (exactRationalLiteral (109263302762422467) 51200000000000000000),
            (exactRationalLiteral (6967956636281029) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-61101456377234525027) 9830400000000000000000),
            (exactRationalLiteral (312317297266976011) 102400000000000000000),
            (exactRationalLiteral (4264354481738893) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-657820996681325921) 131072000000000000000),
            (exactRationalLiteral (-6910010215698377) 20480000000000000000),
            (exactRationalLiteral (1603969968688773) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-86425840571827864267) 9830400000000000000000),
            (exactRationalLiteral (-19227415701925261) 102400000000000000000),
            (exactRationalLiteral (-956149470776539) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2575931690822341) 81920000000000000000),
            (exactRationalLiteral (2584759035168511) 12800000000000000000),
            (exactRationalLiteral (122098501719309) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (3140250659233926737) 2457600000000000000000),
            (exactRationalLiteral (19330800985199839) 25600000000000000000),
            (exactRationalLiteral (109735538546609) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (95766519725973157) 3276800000000000000000),
            (exactRationalLiteral (2259548027619541) 20480000000000000000),
            (exactRationalLiteral (-181226872085121) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2401861533642180503) 4915200000000000000000),
            (exactRationalLiteral (-2492955362619201) 51200000000000000000),
            (exactRationalLiteral (419271318869593) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4067688552138725633) 9830400000000000000000),
            (exactRationalLiteral (-33350623839221031) 102400000000000000000),
            (exactRationalLiteral (-3722998305174257) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-3168180842987568191) 3276800000000000000000),
            (exactRationalLiteral (17844075788845969) 20480000000000000000),
            (exactRationalLiteral (13951510633032147) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (21753192673187143) 245760000000000000000),
            (exactRationalLiteral (-90164790327184971) 12800000000000000000),
            (exactRationalLiteral (-8060120036340493) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-114554738713353481499) 9830400000000000000000),
            (exactRationalLiteral (334598401408001351) 20480000000000000000),
            (exactRationalLiteral (243456103212533653) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (91027041658859557307) 1638400000000000000000),
            (exactRationalLiteral (1935274319328714759) 51200000000000000000),
            (exactRationalLiteral (-226702488070478847) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-495471466537613747923) 9830400000000000000000),
            (exactRationalLiteral (-13466864901078014309) 102400000000000000000),
            (exactRationalLiteral (384359606837602013) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18051988040440003779) 1638400000000000000000),
            (exactRationalLiteral (6006076885048471473) 51200000000000000000),
            (exactRationalLiteral (-49155562787742297) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (7039257571608013639) 393216000000000000000),
            (exactRationalLiteral (-3192421145272617911) 102400000000000000000),
            (exactRationalLiteral (-1773483146511593) 128000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (596205520162067151) 3276800000000000000000),
            (exactRationalLiteral (-198735173387355717) 102400000000000000000),
            (exactRationalLiteral (22081685931928413) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (2453520659103157) 9830400000000000000),
          (exactRationalLiteral (7725459675332271161) 409600000000000000000),
          (exactRationalLiteral (602529841108324891) 40960000000000000000),
          (exactRationalLiteral (348093611998101749) 6400000000000000000),
          (exactRationalLiteral (543338777538939403) 9600000000000000000),
          (exactRationalLiteral (4952411524722078877) 409600000000000000000),
          (exactRationalLiteral (44442171195772303) 153600000000000000000),
          (exactRationalLiteral (243279997964809757) 245760000000000000000),
          (exactRationalLiteral (8162401870381181) 19200000000000000000),
          (exactRationalLiteral (313548096604493) 640000000000000000),
          (exactRationalLiteral (25049674987027) 768000000000000000),
          (exactRationalLiteral (312359709077623) 240000000000000000),
          (exactRationalLiteral (5755041146179961) 153600000000000000000),
          (exactRationalLiteral (56306360013884089) 6400000000000000000),
          (exactRationalLiteral (96553199800574603) 19200000000000000000),
          (exactRationalLiteral (7753190854713945263) 1228800000000000000000),
          (exactRationalLiteral (842843314330252641) 40960000000000000000),
          (exactRationalLiteral (317183706820652149) 4800000000000000000),
          (exactRationalLiteral (2552270792213355429) 6400000000000000000),
          (exactRationalLiteral (15573941528997026797) 9600000000000000000),
          (exactRationalLiteral (6111253019788449289) 19200000000000000000),
          (exactRationalLiteral (829870238144410956911) 307200000000000000000),
          (exactRationalLiteral (81803161751802987763) 38400000000000000000),
          (exactRationalLiteral (1208105100321852376321) 614400000000000000000),
          (exactRationalLiteral (892903590776722488791) 307200000000000000000),
          (exactRationalLiteral (1208105100321852376321) 614400000000000000000),
          (exactRationalLiteral (81803161751802987763) 38400000000000000000),
          (exactRationalLiteral (829870238144410956911) 307200000000000000000),
          (exactRationalLiteral (6111253019788449289) 19200000000000000000),
          (exactRationalLiteral (15573941528997026797) 9600000000000000000),
          (exactRationalLiteral (2552270792213355429) 6400000000000000000),
          (exactRationalLiteral (317183706820652149) 4800000000000000000),
          (exactRationalLiteral (842843314330252641) 40960000000000000000),
          (exactRationalLiteral (7753190854713945263) 1228800000000000000000),
          (exactRationalLiteral (96553199800574603) 19200000000000000000),
          (exactRationalLiteral (56306360013884089) 6400000000000000000),
          (exactRationalLiteral (5755041146179961) 153600000000000000000),
          (exactRationalLiteral (312359709077623) 240000000000000000),
          (exactRationalLiteral (25049674987027) 768000000000000000),
          (exactRationalLiteral (313548096604493) 640000000000000000),
          (exactRationalLiteral (8162401870381181) 19200000000000000000),
          (exactRationalLiteral (243279997964809757) 245760000000000000000),
          (exactRationalLiteral (44442171195772303) 153600000000000000000),
          (exactRationalLiteral (4952411524722078877) 409600000000000000000),
          (exactRationalLiteral (543338777538939403) 9600000000000000000),
          (exactRationalLiteral (348093611998101749) 6400000000000000000),
          (exactRationalLiteral (602529841108324891) 40960000000000000000),
          (exactRationalLiteral (7725459675332271161) 409600000000000000000),
          (exactRationalLiteral (2453520659103157) 9830400000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 43),
      (30, 27),
      (30, 11),
      (29, 59),
      (29, 43),
      (29, 27),
      (29, 11),
      (28, 59),
      (28, 43),
      (28, 27),
      (28, 11),
      (27, 59),
      (27, 43),
      (27, 27),
      (27, 11),
      (26, 59),
      (26, 43),
      (26, 27),
      (26, 11),
      (25, 59),
      (25, 43),
      (25, 27),
      (25, 11),
      (24, 59),
      (24, 43),
      (24, 27),
      (24, 11),
      (23, 59),
      (23, 43),
      (23, 27),
      (23, 20),
      (23, 36),
      (23, 52),
      (24, 4),
      (24, 20),
      (24, 36),
      (24, 52),
      (25, 4),
      (25, 20),
      (25, 36),
      (25, 52),
      (26, 4),
      (26, 20),
      (26, 36),
      (26, 52),
      (27, 4),
      (27, 20),
      (27, 36),
      (27, 52),
      (28, 4),
      (28, 20),
      (28, 36),
      (28, 52)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
theorem generatorCoordinates16_valid : ∀ i, (generatorCoordinates16 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
