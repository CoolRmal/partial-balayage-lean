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

/-- Actual coordinate interval candidates, block 21. -/
def generatorCoordinates21 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 4
        lower := (exactRationalLiteral (15) 16)
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
            (exactRationalLiteral (684347342461457) 2457600000000000000000),
            (exactRationalLiteral (-684347342461457) 25600000000000000000),
            (exactRationalLiteral (684347342461457) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (7306409342555457799) 655360000000000000000),
            (exactRationalLiteral (-660467671794573141) 20480000000000000000),
            (exactRationalLiteral (16262812525730709) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (78519160812611974381) 4915200000000000000000),
            (exactRationalLiteral (4512052298153033923) 51200000000000000000),
            (exactRationalLiteral (-215042453030803571) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-50644344917075887699) 614400000000000000000),
            (exactRationalLiteral (-299039485539088063) 6400000000000000000),
            (exactRationalLiteral (2103213719631929) 8000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (309298630004826680323) 4915200000000000000000),
            (exactRationalLiteral (-612247986032645591) 10240000000000000000),
            (exactRationalLiteral (-402510993268029341) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7669173354272872151) 1638400000000000000000),
            (exactRationalLiteral (3541934395273855013) 51200000000000000000),
            (exactRationalLiteral (7923904974976371) 64000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-591635461789785937) 245760000000000000000),
            (exactRationalLiteral (-269033443391263699) 12800000000000000000),
            (exactRationalLiteral (-2605963256198593) 80000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-6427080820811469377) 9830400000000000000000),
            (exactRationalLiteral (81980979560438221) 20480000000000000000),
            (exactRationalLiteral (22974338753744959) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-6906741493434464563) 9830400000000000000000),
            (exactRationalLiteral (-147127812830442029) 102400000000000000000),
            (exactRationalLiteral (-6681847226420851) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2830227845733294817) 9830400000000000000000),
            (exactRationalLiteral (69316367821597791) 102400000000000000000),
            (exactRationalLiteral (462400229289389) 640000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10987050389554767533) 4915200000000000000000),
            (exactRationalLiteral (32622957603033347) 51200000000000000000),
            (exactRationalLiteral (-336202416910003) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5134633521171886097) 4915200000000000000000),
            (exactRationalLiteral (79538774224024191) 51200000000000000000),
            (exactRationalLiteral (839111419881713) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-25021878782586180169) 2457600000000000000000),
            (exactRationalLiteral (-2313898863539679) 1024000000000000000),
            (exactRationalLiteral (-817210595058217) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-43516904861091663109) 9830400000000000000000),
            (exactRationalLiteral (85734968050951141) 102400000000000000000),
            (exactRationalLiteral (-683879413313221) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10962217094170437223) 9830400000000000000000),
            (exactRationalLiteral (88530289558571483) 20480000000000000000),
            (exactRationalLiteral (-1509896217954343) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-38047371866837338633) 3276800000000000000000),
            (exactRationalLiteral (945325046191943963) 102400000000000000000),
            (exactRationalLiteral (-3776814319297563) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-127180830378050339367) 3276800000000000000000),
            (exactRationalLiteral (3519673585476101077) 102400000000000000000),
            (exactRationalLiteral (-7721804407600437) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-182321394337620591847) 4915200000000000000000),
            (exactRationalLiteral (16616197337279799143) 51200000000000000000),
            (exactRationalLiteral (-550624246155313639) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (38530627893092687113) 51200000000000000000),
            (exactRationalLiteral (-323441967932787009) 200000000000000000),
            (exactRationalLiteral (61938202912061109) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-9846133846772160867697) 9830400000000000000000),
            (exactRationalLiteral (220384835769391834289) 102400000000000000000),
            (exactRationalLiteral (-4829422876659076081) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1810642308106518942091) 4915200000000000000000),
            (exactRationalLiteral (-53525382225882396011) 51200000000000000000),
            (exactRationalLiteral (1086917529285750091) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-74443175013792794873) 2457600000000000000000),
            (exactRationalLiteral (2983689688770333537) 25600000000000000000),
            (exactRationalLiteral (-2223555590655733) 160000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1540194213866507422287) 3276800000000000000000),
            (exactRationalLiteral (35554414588525267501) 102400000000000000000),
            (exactRationalLiteral (-121032011217732681) 640000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2366616896995227363043) 2457600000000000000000),
            (exactRationalLiteral (-16757641147120366531) 25600000000000000000),
            (exactRationalLiteral (228793326116137123) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1540194213866507422287) 3276800000000000000000),
            (exactRationalLiteral (35554414588525267501) 102400000000000000000),
            (exactRationalLiteral (-121032011217732681) 640000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-74443175013792794873) 2457600000000000000000),
            (exactRationalLiteral (2983689688770333537) 25600000000000000000),
            (exactRationalLiteral (-2223555590655733) 160000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1810642308106518942091) 4915200000000000000000),
            (exactRationalLiteral (-53525382225882396011) 51200000000000000000),
            (exactRationalLiteral (1086917529285750091) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9846133846772160867697) 9830400000000000000000),
            (exactRationalLiteral (220384835769391834289) 102400000000000000000),
            (exactRationalLiteral (-4829422876659076081) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (38530627893092687113) 51200000000000000000),
            (exactRationalLiteral (-323441967932787009) 200000000000000000),
            (exactRationalLiteral (61938202912061109) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-182321394337620591847) 4915200000000000000000),
            (exactRationalLiteral (16616197337279799143) 51200000000000000000),
            (exactRationalLiteral (-550624246155313639) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-127180830378050339367) 3276800000000000000000),
            (exactRationalLiteral (3519673585476101077) 102400000000000000000),
            (exactRationalLiteral (-7721804407600437) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-38047371866837338633) 3276800000000000000000),
            (exactRationalLiteral (945325046191943963) 102400000000000000000),
            (exactRationalLiteral (-3776814319297563) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10962217094170437223) 9830400000000000000000),
            (exactRationalLiteral (88530289558571483) 20480000000000000000),
            (exactRationalLiteral (-1509896217954343) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-43516904861091663109) 9830400000000000000000),
            (exactRationalLiteral (85734968050951141) 102400000000000000000),
            (exactRationalLiteral (-683879413313221) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-25021878782586180169) 2457600000000000000000),
            (exactRationalLiteral (-2313898863539679) 1024000000000000000),
            (exactRationalLiteral (-817210595058217) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (5134633521171886097) 4915200000000000000000),
            (exactRationalLiteral (79538774224024191) 51200000000000000000),
            (exactRationalLiteral (839111419881713) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (10987050389554767533) 4915200000000000000000),
            (exactRationalLiteral (32622957603033347) 51200000000000000000),
            (exactRationalLiteral (-336202416910003) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2830227845733294817) 9830400000000000000000),
            (exactRationalLiteral (69316367821597791) 102400000000000000000),
            (exactRationalLiteral (462400229289389) 640000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6906741493434464563) 9830400000000000000000),
            (exactRationalLiteral (-147127812830442029) 102400000000000000000),
            (exactRationalLiteral (-6681847226420851) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-6427080820811469377) 9830400000000000000000),
            (exactRationalLiteral (81980979560438221) 20480000000000000000),
            (exactRationalLiteral (22974338753744959) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-591635461789785937) 245760000000000000000),
            (exactRationalLiteral (-269033443391263699) 12800000000000000000),
            (exactRationalLiteral (-2605963256198593) 80000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-7669173354272872151) 1638400000000000000000),
            (exactRationalLiteral (3541934395273855013) 51200000000000000000),
            (exactRationalLiteral (7923904974976371) 64000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (309298630004826680323) 4915200000000000000000),
            (exactRationalLiteral (-612247986032645591) 10240000000000000000),
            (exactRationalLiteral (-402510993268029341) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-50644344917075887699) 614400000000000000000),
            (exactRationalLiteral (-299039485539088063) 6400000000000000000),
            (exactRationalLiteral (2103213719631929) 8000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (78519160812611974381) 4915200000000000000000),
            (exactRationalLiteral (4512052298153033923) 51200000000000000000),
            (exactRationalLiteral (-215042453030803571) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (7306409342555457799) 655360000000000000000),
            (exactRationalLiteral (-660467671794573141) 20480000000000000000),
            (exactRationalLiteral (16262812525730709) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 2457600000000000000000),
            (exactRationalLiteral (-684347342461457) 25600000000000000000),
            (exactRationalLiteral (684347342461457) 800000000000000000),
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
          (exactRationalLiteral (684347342461457) 307200000000000000000),
          (exactRationalLiteral (997756705574218023) 81920000000000000000),
          (exactRationalLiteral (5578015341029527) 300000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (39661729621306362187) 614400000000000000000),
          (exactRationalLiteral (4130873975715092213) 614400000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (948600434779392097) 1228800000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (1824001536814279879) 409600000000000000000),
          (exactRationalLiteral (1536817564405231543) 1228800000000000000000),
          (exactRationalLiteral (584943599744753363) 49152000000000000000),
          (exactRationalLiteral (49015201177366305157) 1228800000000000000000),
          (exactRationalLiteral (29221999195168653991) 614400000000000000000),
          (exactRationalLiteral (1235325392089480229) 1536000000000000000),
          (exactRationalLiteral (438368054451679857691) 409600000000000000000),
          (exactRationalLiteral (82252489899761331401) 204800000000000000000),
          (exactRationalLiteral (10416934271434026581) 307200000000000000000),
          (exactRationalLiteral (591147683038090037197) 1228800000000000000000),
          (exactRationalLiteral (302200050563704944691) 307200000000000000000),
          (exactRationalLiteral (591147683038090037197) 1228800000000000000000),
          (exactRationalLiteral (10416934271434026581) 307200000000000000000),
          (exactRationalLiteral (82252489899761331401) 204800000000000000000),
          (exactRationalLiteral (438368054451679857691) 409600000000000000000),
          (exactRationalLiteral (1235325392089480229) 1536000000000000000),
          (exactRationalLiteral (29221999195168653991) 614400000000000000000),
          (exactRationalLiteral (49015201177366305157) 1228800000000000000000),
          (exactRationalLiteral (584943599744753363) 49152000000000000000),
          (exactRationalLiteral (1536817564405231543) 1228800000000000000000),
          (exactRationalLiteral (1824001536814279879) 409600000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (948600434779392097) 1228800000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (4130873975715092213) 614400000000000000000),
          (exactRationalLiteral (39661729621306362187) 614400000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (5578015341029527) 300000000000000000),
          (exactRationalLiteral (997756705574218023) 81920000000000000000),
          (exactRationalLiteral (684347342461457) 307200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (30, 63),
      (30, 47),
      (30, 31),
      (30, 15),
      (29, 63),
      (29, 47),
      (29, 31),
      (29, 15),
      (28, 63),
      (28, 47),
      (28, 31),
      (28, 15),
      (27, 63),
      (27, 47),
      (27, 31),
      (27, 15),
      (26, 63),
      (26, 47),
      (26, 31),
      (26, 15),
      (25, 63),
      (25, 47),
      (25, 31),
      (25, 15),
      (24, 63),
      (24, 47),
      (24, 31),
      (24, 15),
      (23, 63),
      (23, 47),
      (23, 31),
      (23, 16),
      (23, 32),
      (23, 48),
      (24, 0),
      (24, 16),
      (24, 32),
      (24, 48),
      (25, 0),
      (25, 16),
      (25, 32),
      (25, 48),
      (26, 0),
      (26, 16),
      (26, 32),
      (26, 48),
      (27, 0),
      (27, 16),
      (27, 32),
      (27, 48),
      (28, 0),
      (28, 16),
      (28, 32)
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
        lower := (exactRationalLiteral (11) 16)
        width := (exactRationalLiteral (1) 32)
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
            (exactRationalLiteral (4693938421943133563) 19660800000000000000000),
            (exactRationalLiteral (-247049390628585977) 102400000000000000000),
            (exactRationalLiteral (13002599506767683) 1600000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (107426568510795180237) 5242880000000000000000),
            (exactRationalLiteral (-2806021900418838621) 81920000000000000000),
            (exactRationalLiteral (-22869671331429297) 1280000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-566992862171189043361) 39321600000000000000000),
            (exactRationalLiteral (26894852839498103579) 204800000000000000000),
            (exactRationalLiteral (-90305896696390969) 3200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-89633501171463529177) 1638400000000000000000),
            (exactRationalLiteral (-3834908678836421379) 25600000000000000000),
            (exactRationalLiteral (50059945587819381) 400000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (2494373944678595667313) 39321600000000000000000),
            (exactRationalLiteral (9628963044311518709) 204800000000000000000),
            (exactRationalLiteral (-96335870515899211) 640000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-602228003064380645207) 39321600000000000000000),
            (exactRationalLiteral (599590490505835209) 40960000000000000000),
            (exactRationalLiteral (260850935284489921) 3200000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (741119637070841759) 655360000000000000000),
            (exactRationalLiteral (-336758737462125563) 51200000000000000000),
            (exactRationalLiteral (-17433016620539319) 800000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-99773648426575166923) 78643200000000000000000),
            (exactRationalLiteral (346417856391176937) 409600000000000000000),
            (exactRationalLiteral (30122012775897581) 6400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-35539599776964764753) 78643200000000000000000),
            (exactRationalLiteral (-41965380264024561) 81920000000000000000),
            (exactRationalLiteral (-8911855547255081) 6400000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (4032081683083933241) 26214400000000000000000),
            (exactRationalLiteral (144405197383740791) 409600000000000000000),
            (exactRationalLiteral (3191307936673779) 6400000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (80721169712627308703) 39321600000000000000000),
            (exactRationalLiteral (29931602033227231) 40960000000000000000),
            (exactRationalLiteral (-91003500930149) 640000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8775629474589468953) 13107200000000000000000),
            (exactRationalLiteral (51975445315659083) 40960000000000000000),
            (exactRationalLiteral (1749887178930771) 3200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-189762928896122097203) 19660800000000000000000),
            (exactRationalLiteral (-7099277535237847) 4096000000000000000),
            (exactRationalLiteral (-1536634573002491) 1600000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-122066417600016089821) 26214400000000000000000),
            (exactRationalLiteral (353457409146503981) 409600000000000000000),
            (exactRationalLiteral (749080182938241) 6400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-179827710493547229517) 78643200000000000000000),
            (exactRationalLiteral (1826862166257500767) 409600000000000000000),
            (exactRationalLiteral (-57881219713217) 1280000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-221817414412169238037) 15728640000000000000000),
            (exactRationalLiteral (3835467194005393683) 409600000000000000000),
            (exactRationalLiteral (4367333977558783) 6400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3768670430978541267943) 78643200000000000000000),
            (exactRationalLiteral (13717158313705313181) 409600000000000000000),
            (exactRationalLiteral (7342086800676541) 1280000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5577720522268039034029) 39321600000000000000000),
            (exactRationalLiteral (90652100907014725439) 204800000000000000000),
            (exactRationalLiteral (-321534540506756773) 3200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (38045933165172937771) 30720000000000000000),
            (exactRationalLiteral (-6158738669960277451) 3200000000000000000),
            (exactRationalLiteral (-2037713719686869) 25000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-42489095223321576061129) 26214400000000000000000),
            (exactRationalLiteral (937321812261247400217) 409600000000000000000),
            (exactRationalLiteral (6377524036631089629) 6400000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8409424892206963748339) 13107200000000000000000),
            (exactRationalLiteral (-33358187024959650567) 40960000000000000000),
            (exactRationalLiteral (-4956811163202754959) 3200000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-770894833230134888939) 19660800000000000000000),
            (exactRationalLiteral (-13932849424115758791) 102400000000000000000),
            (exactRationalLiteral (1543859566447562797) 1600000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-45857154509786272328623) 78643200000000000000000),
            (exactRationalLiteral (218077087090082962677) 409600000000000000000),
            (exactRationalLiteral (-3251999225233372759) 6400000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22867136314734039596449) 19660800000000000000000),
            (exactRationalLiteral (-17916698826690865727) 20480000000000000000),
            (exactRationalLiteral (869056262177894137) 1600000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-45857154509786272328623) 78643200000000000000000),
            (exactRationalLiteral (218077087090082962677) 409600000000000000000),
            (exactRationalLiteral (-3251999225233372759) 6400000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-770894833230134888939) 19660800000000000000000),
            (exactRationalLiteral (-13932849424115758791) 102400000000000000000),
            (exactRationalLiteral (1543859566447562797) 1600000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (8409424892206963748339) 13107200000000000000000),
            (exactRationalLiteral (-33358187024959650567) 40960000000000000000),
            (exactRationalLiteral (-4956811163202754959) 3200000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-42489095223321576061129) 26214400000000000000000),
            (exactRationalLiteral (937321812261247400217) 409600000000000000000),
            (exactRationalLiteral (6377524036631089629) 6400000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (38045933165172937771) 30720000000000000000),
            (exactRationalLiteral (-6158738669960277451) 3200000000000000000),
            (exactRationalLiteral (-2037713719686869) 25000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-5577720522268039034029) 39321600000000000000000),
            (exactRationalLiteral (90652100907014725439) 204800000000000000000),
            (exactRationalLiteral (-321534540506756773) 3200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3768670430978541267943) 78643200000000000000000),
            (exactRationalLiteral (13717158313705313181) 409600000000000000000),
            (exactRationalLiteral (7342086800676541) 1280000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-221817414412169238037) 15728640000000000000000),
            (exactRationalLiteral (3835467194005393683) 409600000000000000000),
            (exactRationalLiteral (4367333977558783) 6400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-179827710493547229517) 78643200000000000000000),
            (exactRationalLiteral (1826862166257500767) 409600000000000000000),
            (exactRationalLiteral (-57881219713217) 1280000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-122066417600016089821) 26214400000000000000000),
            (exactRationalLiteral (353457409146503981) 409600000000000000000),
            (exactRationalLiteral (749080182938241) 6400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-189762928896122097203) 19660800000000000000000),
            (exactRationalLiteral (-7099277535237847) 4096000000000000000),
            (exactRationalLiteral (-1536634573002491) 1600000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (8775629474589468953) 13107200000000000000000),
            (exactRationalLiteral (51975445315659083) 40960000000000000000),
            (exactRationalLiteral (1749887178930771) 3200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (80721169712627308703) 39321600000000000000000),
            (exactRationalLiteral (29931602033227231) 40960000000000000000),
            (exactRationalLiteral (-91003500930149) 640000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4032081683083933241) 26214400000000000000000),
            (exactRationalLiteral (144405197383740791) 409600000000000000000),
            (exactRationalLiteral (3191307936673779) 6400000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-35539599776964764753) 78643200000000000000000),
            (exactRationalLiteral (-41965380264024561) 81920000000000000000),
            (exactRationalLiteral (-8911855547255081) 6400000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-99773648426575166923) 78643200000000000000000),
            (exactRationalLiteral (346417856391176937) 409600000000000000000),
            (exactRationalLiteral (30122012775897581) 6400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (741119637070841759) 655360000000000000000),
            (exactRationalLiteral (-336758737462125563) 51200000000000000000),
            (exactRationalLiteral (-17433016620539319) 800000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-602228003064380645207) 39321600000000000000000),
            (exactRationalLiteral (599590490505835209) 40960000000000000000),
            (exactRationalLiteral (260850935284489921) 3200000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2494373944678595667313) 39321600000000000000000),
            (exactRationalLiteral (9628963044311518709) 204800000000000000000),
            (exactRationalLiteral (-96335870515899211) 640000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-89633501171463529177) 1638400000000000000000),
            (exactRationalLiteral (-3834908678836421379) 25600000000000000000),
            (exactRationalLiteral (50059945587819381) 400000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-566992862171189043361) 39321600000000000000000),
            (exactRationalLiteral (26894852839498103579) 204800000000000000000),
            (exactRationalLiteral (-90305896696390969) 3200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (107426568510795180237) 5242880000000000000000),
            (exactRationalLiteral (-2806021900418838621) 81920000000000000000),
            (exactRationalLiteral (-22869671331429297) 1280000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (4693938421943133563) 19660800000000000000000),
            (exactRationalLiteral (-247049390628585977) 102400000000000000000),
            (exactRationalLiteral (13002599506767683) 1600000000000000000),
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
          (exactRationalLiteral (684347342461457) 2457600000000000000),
          (exactRationalLiteral (1722009914962508939) 81920000000000000000),
          (exactRationalLiteral (10123880490300337999) 614400000000000000000),
          (exactRationalLiteral (35031476061764153771) 614400000000000000000),
          (exactRationalLiteral (105074865649952213081) 1638400000000000000000),
          (exactRationalLiteral (3179412859616242123) 204800000000000000000),
          (exactRationalLiteral (7547049479114963) 6144000000000000000),
          (exactRationalLiteral (1573804170901552093) 1228800000000000000000),
          (exactRationalLiteral (4524509740055462203) 9830400000000000000000),
          (exactRationalLiteral (1567389855168955577) 9830400000000000000000),
          (exactRationalLiteral (135281276505203023) 65536000000000000000),
          (exactRationalLiteral (3388970693686340329) 4915200000000000000000),
          (exactRationalLiteral (4757499759178447277) 491520000000000000000),
          (exactRationalLiteral (5738394582296831681) 1228800000000000000000),
          (exactRationalLiteral (579090639373920031) 245760000000000000000),
          (exactRationalLiteral (5836352450040805349) 409600000000000000000),
          (exactRationalLiteral (19842232847566538427) 409600000000000000000),
          (exactRationalLiteral (3656622226927516739) 24576000000000000000),
          (exactRationalLiteral (16237057705756143991) 12800000000000000000),
          (exactRationalLiteral (2035299612793259064077) 1228800000000000000000),
          (exactRationalLiteral (401771212480123848623) 614400000000000000000),
          (exactRationalLiteral (33673080251901287323) 819200000000000000000),
          (exactRationalLiteral (242298238893247799859) 409600000000000000000),
          (exactRationalLiteral (361539346406494358567) 307200000000000000000),
          (exactRationalLiteral (242298238893247799859) 409600000000000000000),
          (exactRationalLiteral (33673080251901287323) 819200000000000000000),
          (exactRationalLiteral (401771212480123848623) 614400000000000000000),
          (exactRationalLiteral (2035299612793259064077) 1228800000000000000000),
          (exactRationalLiteral (16237057705756143991) 12800000000000000000),
          (exactRationalLiteral (3656622226927516739) 24576000000000000000),
          (exactRationalLiteral (19842232847566538427) 409600000000000000000),
          (exactRationalLiteral (5836352450040805349) 409600000000000000000),
          (exactRationalLiteral (579090639373920031) 245760000000000000000),
          (exactRationalLiteral (5738394582296831681) 1228800000000000000000),
          (exactRationalLiteral (4757499759178447277) 491520000000000000000),
          (exactRationalLiteral (3388970693686340329) 4915200000000000000000),
          (exactRationalLiteral (135281276505203023) 65536000000000000000),
          (exactRationalLiteral (1567389855168955577) 9830400000000000000000),
          (exactRationalLiteral (4524509740055462203) 9830400000000000000000),
          (exactRationalLiteral (1573804170901552093) 1228800000000000000000),
          (exactRationalLiteral (7547049479114963) 6144000000000000000),
          (exactRationalLiteral (3179412859616242123) 204800000000000000000),
          (exactRationalLiteral (105074865649952213081) 1638400000000000000000),
          (exactRationalLiteral (35031476061764153771) 614400000000000000000),
          (exactRationalLiteral (10123880490300337999) 614400000000000000000),
          (exactRationalLiteral (1722009914962508939) 81920000000000000000),
          (exactRationalLiteral (684347342461457) 2457600000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (18, 26),
      (17, 62),
      (17, 34),
      (17, 6),
      (16, 42),
      (16, 10),
      (15, 42),
      (15, 10),
      (14, 42),
      (14, 10),
      (13, 42),
      (13, 10),
      (12, 42),
      (12, 10),
      (11, 42),
      (11, 10),
      (10, 42),
      (10, 10),
      (9, 42),
      (9, 10),
      (8, 42),
      (8, 10),
      (7, 42),
      (7, 10),
      (6, 42),
      (6, 10),
      (5, 42),
      (5, 10),
      (4, 42),
      (4, 10),
      (3, 42),
      (3, 29),
      (3, 61),
      (4, 29),
      (4, 61),
      (5, 29),
      (5, 61),
      (6, 29),
      (6, 61),
      (7, 29),
      (7, 61),
      (8, 29),
      (8, 61),
      (9, 29),
      (9, 61),
      (10, 29),
      (10, 61),
      (11, 29),
      (11, 61),
      (12, 29),
      (12, 61),
      (13, 29),
      (13, 61)
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
        lower := (exactRationalLiteral (23) 32)
        width := (exactRationalLiteral (1) 32)
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
            (exactRationalLiteral (3362198493513138241) 19660800000000000000000),
            (exactRationalLiteral (-197776381971361073) 102400000000000000000),
            (exactRationalLiteral (11633904821844769) 1600000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (101731735482887925527) 5242880000000000000000),
            (exactRationalLiteral (-2884466398360346229) 81920000000000000000),
            (exactRationalLiteral (-16352577639324507) 1280000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-406867311898964274067) 39321600000000000000000),
            (exactRationalLiteral (26453681250508959427) 204800000000000000000),
            (exactRationalLiteral (-130279897798181107) 3200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-291283306480169976377) 4915200000000000000000),
            (exactRationalLiteral (-3621704016392490427) 25600000000000000000),
            (exactRationalLiteral (11308477126829219) 80000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (2546215409474001856259) 39321600000000000000000),
            (exactRationalLiteral (1525233002847809833) 40960000000000000000),
            (exactRationalLiteral (-519719662456738717) 3200000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-193682128561387145863) 13107200000000000000000),
            (exactRationalLiteral (4073201914482271877) 204800000000000000000),
            (exactRationalLiteral (55354759138411599) 640000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1776597269574191143) 1966080000000000000000),
            (exactRationalLiteral (-408520595930505571) 51200000000000000000),
            (exactRationalLiteral (-3689582522730137) 160000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-97326229292690702641) 78643200000000000000000),
            (exactRationalLiteral (94125965721616621) 81920000000000000000),
            (exactRationalLiteral (31983973332555503) 6400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-36907598434466956259) 78643200000000000000000),
            (exactRationalLiteral (-246521815016339981) 409600000000000000000),
            (exactRationalLiteral (-9435601300853507) 6400000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (13001646137903139281) 78643200000000000000000),
            (exactRationalLiteral (157507533684840639) 409600000000000000000),
            (exactRationalLiteral (671972042775229) 1280000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (81613555263648707629) 39321600000000000000000),
            (exactRationalLiteral (147786790187728643) 204800000000000000000),
            (exactRationalLiteral (-480592484553011) 3200000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27907116704990446321) 39321600000000000000000),
            (exactRationalLiteral (266859913096567359) 204800000000000000000),
            (exactRationalLiteral (1741456080205201) 3200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-190846306158515387177) 19660800000000000000000),
            (exactRationalLiteral (-36730297057749531) 20480000000000000000),
            (exactRationalLiteral (-1548138880898249) 1600000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-364070515542507899477) 78643200000000000000000),
            (exactRationalLiteral (355955650111300549) 409600000000000000000),
            (exactRationalLiteral (500040299460043) 6400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-168871295256873179159) 78643200000000000000000),
            (exactRationalLiteral (365012419603831163) 81920000000000000000),
            (exactRationalLiteral (-610628020606391) 6400000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-362009156917947888569) 26214400000000000000000),
            (exactRationalLiteral (3850131597535357307) 409600000000000000000),
            (exactRationalLiteral (2964867787423029) 6400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1228650499655747415831) 26214400000000000000000),
            (exactRationalLiteral (13851728510232118453) 409600000000000000000),
            (exactRationalLiteral (30574664260019931) 6400000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5038033255524645348791) 39321600000000000000000),
            (exactRationalLiteral (89182500638680905287) 204800000000000000000),
            (exactRationalLiteral (-413265593660153303) 3200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (120658065232039507631) 102400000000000000000),
            (exactRationalLiteral (-6159507760811552439) 3200000000000000000),
            (exactRationalLiteral (922720503434061) 12500000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-121774371034917646820321) 78643200000000000000000),
            (exactRationalLiteral (959058644927783701841) 409600000000000000000),
            (exactRationalLiteral (4490892296637061183) 6400000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (24171402930135680082683) 39321600000000000000000),
            (exactRationalLiteral (-184940380666603565579) 204800000000000000000),
            (exactRationalLiteral (-4117911607699901413) 3200000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-836702600917390038769) 19660800000000000000000),
            (exactRationalLiteral (-8125904128291182927) 102400000000000000000),
            (exactRationalLiteral (271922616292945027) 320000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-14862251729259241707231) 26214400000000000000000),
            (exactRationalLiteral (205549485274574423629) 409600000000000000000),
            (exactRationalLiteral (-602360336504179353) 1280000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22339870392321826886099) 19660800000000000000000),
            (exactRationalLiteral (-86204085463553486179) 102400000000000000000),
            (exactRationalLiteral (820648072772527091) 1600000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-14862251729259241707231) 26214400000000000000000),
            (exactRationalLiteral (205549485274574423629) 409600000000000000000),
            (exactRationalLiteral (-602360336504179353) 1280000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-836702600917390038769) 19660800000000000000000),
            (exactRationalLiteral (-8125904128291182927) 102400000000000000000),
            (exactRationalLiteral (271922616292945027) 320000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (24171402930135680082683) 39321600000000000000000),
            (exactRationalLiteral (-184940380666603565579) 204800000000000000000),
            (exactRationalLiteral (-4117911607699901413) 3200000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-121774371034917646820321) 78643200000000000000000),
            (exactRationalLiteral (959058644927783701841) 409600000000000000000),
            (exactRationalLiteral (4490892296637061183) 6400000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (120658065232039507631) 102400000000000000000),
            (exactRationalLiteral (-6159507760811552439) 3200000000000000000),
            (exactRationalLiteral (922720503434061) 12500000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-5038033255524645348791) 39321600000000000000000),
            (exactRationalLiteral (89182500638680905287) 204800000000000000000),
            (exactRationalLiteral (-413265593660153303) 3200000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1228650499655747415831) 26214400000000000000000),
            (exactRationalLiteral (13851728510232118453) 409600000000000000000),
            (exactRationalLiteral (30574664260019931) 6400000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-362009156917947888569) 26214400000000000000000),
            (exactRationalLiteral (3850131597535357307) 409600000000000000000),
            (exactRationalLiteral (2964867787423029) 6400000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-168871295256873179159) 78643200000000000000000),
            (exactRationalLiteral (365012419603831163) 81920000000000000000),
            (exactRationalLiteral (-610628020606391) 6400000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-364070515542507899477) 78643200000000000000000),
            (exactRationalLiteral (355955650111300549) 409600000000000000000),
            (exactRationalLiteral (500040299460043) 6400000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-190846306158515387177) 19660800000000000000000),
            (exactRationalLiteral (-36730297057749531) 20480000000000000000),
            (exactRationalLiteral (-1548138880898249) 1600000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (27907116704990446321) 39321600000000000000000),
            (exactRationalLiteral (266859913096567359) 204800000000000000000),
            (exactRationalLiteral (1741456080205201) 3200000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (81613555263648707629) 39321600000000000000000),
            (exactRationalLiteral (147786790187728643) 204800000000000000000),
            (exactRationalLiteral (-480592484553011) 3200000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (13001646137903139281) 78643200000000000000000),
            (exactRationalLiteral (157507533684840639) 409600000000000000000),
            (exactRationalLiteral (671972042775229) 1280000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-36907598434466956259) 78643200000000000000000),
            (exactRationalLiteral (-246521815016339981) 409600000000000000000),
            (exactRationalLiteral (-9435601300853507) 6400000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-97326229292690702641) 78643200000000000000000),
            (exactRationalLiteral (94125965721616621) 81920000000000000000),
            (exactRationalLiteral (31983973332555503) 6400000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1776597269574191143) 1966080000000000000000),
            (exactRationalLiteral (-408520595930505571) 51200000000000000000),
            (exactRationalLiteral (-3689582522730137) 160000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-193682128561387145863) 13107200000000000000000),
            (exactRationalLiteral (4073201914482271877) 204800000000000000000),
            (exactRationalLiteral (55354759138411599) 640000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2546215409474001856259) 39321600000000000000000),
            (exactRationalLiteral (1525233002847809833) 40960000000000000000),
            (exactRationalLiteral (-519719662456738717) 3200000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-291283306480169976377) 4915200000000000000000),
            (exactRationalLiteral (-3621704016392490427) 25600000000000000000),
            (exactRationalLiteral (11308477126829219) 80000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-406867311898964274067) 39321600000000000000000),
            (exactRationalLiteral (26453681250508959427) 204800000000000000000),
            (exactRationalLiteral (-130279897798181107) 3200000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (101731735482887925527) 5242880000000000000000),
            (exactRationalLiteral (-2884466398360346229) 81920000000000000000),
            (exactRationalLiteral (-16352577639324507) 1280000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (3362198493513138241) 19660800000000000000000),
            (exactRationalLiteral (-197776381971361073) 102400000000000000000),
            (exactRationalLiteral (11633904821844769) 1600000000000000000),
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
          (exactRationalLiteral (166296404218134051) 819200000000000000000),
          (exactRationalLiteral (13074845390165866223) 655360000000000000000),
          (exactRationalLiteral (2432996041716674003) 196608000000000000000),
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (74055453933841982909) 4915200000000000000000),
          (exactRationalLiteral (1256713980727259507) 1228800000000000000000),
          (exactRationalLiteral (12330387229849451801) 9830400000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (45642094731500210237) 9830400000000000000000),
          (exactRationalLiteral (7264506367667976901) 3276800000000000000000),
          (exactRationalLiteral (137196033713749050083) 9830400000000000000000),
          (exactRationalLiteral (465926486577535857709) 9830400000000000000000),
          (exactRationalLiteral (221115612028962159429) 1638400000000000000000),
          (exactRationalLiteral (185608526041496589211) 153600000000000000000),
          (exactRationalLiteral (15579641372117636216009) 9830400000000000000000),
          (exactRationalLiteral (3089181360941829956051) 4915200000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (5651569893427545915109) 9830400000000000000000),
          (exactRationalLiteral (941707033209396150393) 819200000000000000000),
          (exactRationalLiteral (5651569893427545915109) 9830400000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (3089181360941829956051) 4915200000000000000000),
          (exactRationalLiteral (15579641372117636216009) 9830400000000000000000),
          (exactRationalLiteral (185608526041496589211) 153600000000000000000),
          (exactRationalLiteral (221115612028962159429) 1638400000000000000000),
          (exactRationalLiteral (465926486577535857709) 9830400000000000000000),
          (exactRationalLiteral (137196033713749050083) 9830400000000000000000),
          (exactRationalLiteral (7264506367667976901) 3276800000000000000000),
          (exactRationalLiteral (45642094731500210237) 9830400000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (12330387229849451801) 9830400000000000000000),
          (exactRationalLiteral (1256713980727259507) 1228800000000000000000),
          (exactRationalLiteral (74055453933841982909) 4915200000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (2432996041716674003) 196608000000000000000),
          (exactRationalLiteral (13074845390165866223) 655360000000000000000),
          (exactRationalLiteral (166296404218134051) 819200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (18, 27),
      (17, 63),
      (17, 35),
      (17, 7),
      (16, 43),
      (16, 11),
      (15, 43),
      (15, 11),
      (14, 43),
      (14, 11),
      (13, 43),
      (13, 11),
      (12, 43),
      (12, 11),
      (11, 43),
      (11, 11),
      (10, 43),
      (10, 11),
      (9, 43),
      (9, 11),
      (8, 43),
      (8, 11),
      (7, 43),
      (7, 11),
      (6, 43),
      (6, 11),
      (5, 43),
      (5, 11),
      (4, 43),
      (4, 11),
      (3, 43),
      (3, 28),
      (3, 60),
      (4, 28),
      (4, 60),
      (5, 28),
      (5, 60),
      (6, 28),
      (6, 60),
      (7, 28),
      (7, 60),
      (8, 28),
      (8, 60),
      (9, 28),
      (9, 60),
      (10, 28),
      (10, 60),
      (11, 28),
      (11, 60),
      (12, 28),
      (12, 60),
      (13, 28),
      (13, 60)
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
        cell := 5
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
            (exactRationalLiteral (101673746728037) 80000000000000000),
            (exactRationalLiteral (-305021240184111) 40000000000000000),
            (exactRationalLiteral (305021240184111) 20000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (13951595321800177) 480000000000000000),
            (exactRationalLiteral (-8955908039343809) 400000000000000000),
            (exactRationalLiteral (-11311448150541883) 200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-56497280585932279) 1200000000000000000),
            (exactRationalLiteral (13929644412328717) 100000000000000000),
            (exactRationalLiteral (5905931678124401) 100000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-15527045342269299) 800000000000000000),
            (exactRationalLiteral (-79123790736904899) 400000000000000000),
            (exactRationalLiteral (3921368973597591) 200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (2560252551045139) 50000000000000000),
            (exactRationalLiteral (10307189575725983) 100000000000000000),
            (exactRationalLiteral (-959841252297777) 12500000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-9619210622189731) 600000000000000000),
            (exactRationalLiteral (-725222753133811) 50000000000000000),
            (exactRationalLiteral (2551091621783813) 50000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (431906134484819) 240000000000000000),
            (exactRationalLiteral (254091790568393) 200000000000000000),
            (exactRationalLiteral (-1385106764316749) 100000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3943204762238119) 2400000000000000000),
            (exactRationalLiteral (-454402794945921) 400000000000000000),
            (exactRationalLiteral (607522602755657) 200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1698624044589917) 2400000000000000000),
            (exactRationalLiteral (227082810740473) 400000000000000000),
            (exactRationalLiteral (-211843294001179) 200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (6214262043337927) 2400000000000000000),
            (exactRationalLiteral (346798693531713) 400000000000000000),
            (exactRationalLiteral (140908640645119) 200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (98620359819877) 50000000000000000),
            (exactRationalLiteral (367790658658327) 200000000000000000),
            (exactRationalLiteral (-406940259957) 25000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6973828138012493) 600000000000000000),
            (exactRationalLiteral (-76454978663393) 25000000000000000),
            (exactRationalLiteral (-22011129822893) 50000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-207441334529247) 50000000000000000),
            (exactRationalLiteral (-1411817157599) 200000000000000000),
            (exactRationalLiteral (-8792864988579) 6250000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (651984026313443) 600000000000000000),
            (exactRationalLiteral (816117645834223) 200000000000000000),
            (exactRationalLiteral (4989555795689) 50000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2828606563943157) 400000000000000000),
            (exactRationalLiteral (1582332941642417) 200000000000000000),
            (exactRationalLiteral (-107943280678743) 100000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-52810068625084627) 2400000000000000000),
            (exactRationalLiteral (11089999049246023) 400000000000000000),
            (exactRationalLiteral (-1912059791850499) 200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (56830947744511799) 1200000000000000000),
            (exactRationalLiteral (6015824751752943) 200000000000000000),
            (exactRationalLiteral (-17129671164966913) 100000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (68432035768554923) 300000000000000000),
            (exactRationalLiteral (-47818098895086333) 100000000000000000),
            (exactRationalLiteral (8992675750327267) 12500000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-699109075468845169) 2400000000000000000),
            (exactRationalLiteral (268954027664325083) 400000000000000000),
            (exactRationalLiteral (-189713371552781257) 200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (273488472822671) 7500000000000000),
            (exactRationalLiteral (-28114730515262333) 100000000000000000),
            (exactRationalLiteral (6072010963452307) 12500000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (6475943120289073) 2400000000000000000),
            (exactRationalLiteral (6699278340757991) 400000000000000000),
            (exactRationalLiteral (-12323761710135719) 200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-259604446661511263) 800000000000000000),
            (exactRationalLiteral (84696495024212159) 400000000000000000),
            (exactRationalLiteral (-19612929553855701) 200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (817167956189846509) 1200000000000000000),
            (exactRationalLiteral (-84689816179514471) 200000000000000000),
            (exactRationalLiteral (3453960024996353) 20000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-259604446661511263) 800000000000000000),
            (exactRationalLiteral (84696495024212159) 400000000000000000),
            (exactRationalLiteral (-19612929553855701) 200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6475943120289073) 2400000000000000000),
            (exactRationalLiteral (6699278340757991) 400000000000000000),
            (exactRationalLiteral (-12323761710135719) 200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (273488472822671) 7500000000000000),
            (exactRationalLiteral (-28114730515262333) 100000000000000000),
            (exactRationalLiteral (6072010963452307) 12500000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-699109075468845169) 2400000000000000000),
            (exactRationalLiteral (268954027664325083) 400000000000000000),
            (exactRationalLiteral (-189713371552781257) 200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (68432035768554923) 300000000000000000),
            (exactRationalLiteral (-47818098895086333) 100000000000000000),
            (exactRationalLiteral (8992675750327267) 12500000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (56830947744511799) 1200000000000000000),
            (exactRationalLiteral (6015824751752943) 200000000000000000),
            (exactRationalLiteral (-17129671164966913) 100000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-52810068625084627) 2400000000000000000),
            (exactRationalLiteral (11089999049246023) 400000000000000000),
            (exactRationalLiteral (-1912059791850499) 200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-2828606563943157) 400000000000000000),
            (exactRationalLiteral (1582332941642417) 200000000000000000),
            (exactRationalLiteral (-107943280678743) 100000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (651984026313443) 600000000000000000),
            (exactRationalLiteral (816117645834223) 200000000000000000),
            (exactRationalLiteral (4989555795689) 50000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-207441334529247) 50000000000000000),
            (exactRationalLiteral (-1411817157599) 200000000000000000),
            (exactRationalLiteral (-8792864988579) 6250000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6973828138012493) 600000000000000000),
            (exactRationalLiteral (-76454978663393) 25000000000000000),
            (exactRationalLiteral (-22011129822893) 50000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (98620359819877) 50000000000000000),
            (exactRationalLiteral (367790658658327) 200000000000000000),
            (exactRationalLiteral (-406940259957) 25000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6214262043337927) 2400000000000000000),
            (exactRationalLiteral (346798693531713) 400000000000000000),
            (exactRationalLiteral (140908640645119) 200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1698624044589917) 2400000000000000000),
            (exactRationalLiteral (227082810740473) 400000000000000000),
            (exactRationalLiteral (-211843294001179) 200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3943204762238119) 2400000000000000000),
            (exactRationalLiteral (-454402794945921) 400000000000000000),
            (exactRationalLiteral (607522602755657) 200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (431906134484819) 240000000000000000),
            (exactRationalLiteral (254091790568393) 200000000000000000),
            (exactRationalLiteral (-1385106764316749) 100000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9619210622189731) 600000000000000000),
            (exactRationalLiteral (-725222753133811) 50000000000000000),
            (exactRationalLiteral (2551091621783813) 50000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2560252551045139) 50000000000000000),
            (exactRationalLiteral (10307189575725983) 100000000000000000),
            (exactRationalLiteral (-959841252297777) 12500000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-15527045342269299) 800000000000000000),
            (exactRationalLiteral (-79123790736904899) 400000000000000000),
            (exactRationalLiteral (3921368973597591) 200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-56497280585932279) 1200000000000000000),
            (exactRationalLiteral (13929644412328717) 100000000000000000),
            (exactRationalLiteral (5905931678124401) 100000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (13951595321800177) 480000000000000000),
            (exactRationalLiteral (-8955908039343809) 400000000000000000),
            (exactRationalLiteral (-11311448150541883) 200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 80000000000000000),
            (exactRationalLiteral (-305021240184111) 40000000000000000),
            (exactRationalLiteral (305021240184111) 20000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (exactRationalLiteral (1688946349157141) 37500000000000000),
          (exactRationalLiteral (14033418864696313) 150000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (6893536957777301) 75000000000000000),
          (exactRationalLiteral (37216661263997) 1250000000000000),
          (exactRationalLiteral (247119883807429) 50000000000000000),
          (exactRationalLiteral (125971568107221) 50000000000000000),
          (exactRationalLiteral (19524693544127) 18750000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (1698580507476641) 150000000000000000),
          (exactRationalLiteral (11322317617059851) 300000000000000000),
          (exactRationalLiteral (110119667235637) 1500000000000000),
          (exactRationalLiteral (52745535823769759) 75000000000000000),
          (exactRationalLiteral (70193564788543393) 75000000000000000),
          (exactRationalLiteral (6308541732004091) 18750000000000000),
          (exactRationalLiteral (2669986268059613) 100000000000000000),
          (exactRationalLiteral (68902813403791141) 150000000000000000),
          (exactRationalLiteral (23569805393854899) 25000000000000000),
          (exactRationalLiteral (68902813403791141) 150000000000000000),
          (exactRationalLiteral (2669986268059613) 100000000000000000),
          (exactRationalLiteral (6308541732004091) 18750000000000000),
          (exactRationalLiteral (70193564788543393) 75000000000000000),
          (exactRationalLiteral (52745535823769759) 75000000000000000),
          (exactRationalLiteral (110119667235637) 1500000000000000),
          (exactRationalLiteral (11322317617059851) 300000000000000000),
          (exactRationalLiteral (1698580507476641) 150000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (19524693544127) 18750000000000000),
          (exactRationalLiteral (125971568107221) 50000000000000000),
          (exactRationalLiteral (247119883807429) 50000000000000000),
          (exactRationalLiteral (37216661263997) 1250000000000000),
          (exactRationalLiteral (6893536957777301) 75000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (14033418864696313) 150000000000000000),
          (exactRationalLiteral (1688946349157141) 37500000000000000),
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (46, 15),
      (46, 16)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 5
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
            (exactRationalLiteral (2745191161656999) 640000000000000000),
            (exactRationalLiteral (-2745191161656999) 160000000000000000),
            (exactRationalLiteral (915063720552333) 40000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (579598786893711043) 19200000000000000000),
            (exactRationalLiteral (27489393991962743) 1600000000000000000),
            (exactRationalLiteral (-40690129848254213) 400000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-182212317671436161) 2400000000000000000),
            (exactRationalLiteral (32904289378637871) 400000000000000000),
            (exactRationalLiteral (4227089148138149) 25000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (181250617323517411) 6400000000000000000),
            (exactRationalLiteral (-55113575268516207) 320000000000000000),
            (exactRationalLiteral (-48770024552233743) 400000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (109340490401234549) 4800000000000000000),
            (exactRationalLiteral (9261501574981743) 80000000000000000),
            (exactRationalLiteral (2599980446377433) 100000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-161616796093603) 16000000000000000),
            (exactRationalLiteral (-5881449427864173) 200000000000000000),
            (exactRationalLiteral (107366698386279) 12500000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2682883763580203) 3200000000000000000),
            (exactRationalLiteral (4424646235471509) 800000000000000000),
            (exactRationalLiteral (-638065544564439) 200000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-23489174051226869) 19200000000000000000),
            (exactRationalLiteral (-3206196481599401) 1600000000000000000),
            (exactRationalLiteral (173540096304403) 400000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (9954549488143273) 19200000000000000000),
            (exactRationalLiteral (1394093794649921) 1600000000000000000),
            (exactRationalLiteral (-62075963685671) 400000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (46213431489190813) 19200000000000000000),
            (exactRationalLiteral (1008092590549137) 1600000000000000000),
            (exactRationalLiteral (97284902287477) 400000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14565663368224753) 9600000000000000000),
            (exactRationalLiteral (1423864925845359) 800000000000000000),
            (exactRationalLiteral (10110646173521) 40000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8713712824864071) 800000000000000000),
            (exactRationalLiteral (-138226387166591) 50000000000000000),
            (exactRationalLiteral (-36723150817887) 50000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-40540486102655941) 9600000000000000000),
            (exactRationalLiteral (441672730666781) 800000000000000000),
            (exactRationalLiteral (-165948319662649) 200000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (636024879618349) 9600000000000000000),
            (exactRationalLiteral (3286736597905711) 800000000000000000),
            (exactRationalLiteral (-1688969510063) 8000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-87554208219437407) 9600000000000000000),
            (exactRationalLiteral (6793100590304817) 800000000000000000),
            (exactRationalLiteral (-247882262377663) 200000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-565795192130836901) 19200000000000000000),
            (exactRationalLiteral (50770531152490703) 1600000000000000000),
            (exactRationalLiteral (-2586415371805613) 400000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (259528718314473767) 9600000000000000000),
            (exactRationalLiteral (22546584659532651) 160000000000000000),
            (exactRationalLiteral (-54410281960717657) 200000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (383657557281926239) 960000000000000000),
            (exactRationalLiteral (-368889016949443627) 400000000000000000),
            (exactRationalLiteral (105675215366480159) 100000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3376561321717524759) 6400000000000000000),
            (exactRationalLiteral (2005752396981649747) 1600000000000000000),
            (exactRationalLiteral (-550509543218786901) 400000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (680923586403615353) 4800000000000000000),
            (exactRationalLiteral (-232397031967388793) 400000000000000000),
            (exactRationalLiteral (14272404439744201) 20000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-116012858788636277) 19200000000000000000),
            (exactRationalLiteral (17915730720922699) 320000000000000000),
            (exactRationalLiteral (-38134016821310093) 400000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-7375245638231871313) 19200000000000000000),
            (exactRationalLiteral (427941099054192327) 1600000000000000000),
            (exactRationalLiteral (-49929259849632289) 400000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7665544098224536249) 9600000000000000000),
            (exactRationalLiteral (-416142319019684879) 800000000000000000),
            (exactRationalLiteral (8568690810332693) 40000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-7375245638231871313) 19200000000000000000),
            (exactRationalLiteral (427941099054192327) 1600000000000000000),
            (exactRationalLiteral (-49929259849632289) 400000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-116012858788636277) 19200000000000000000),
            (exactRationalLiteral (17915730720922699) 320000000000000000),
            (exactRationalLiteral (-38134016821310093) 400000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (680923586403615353) 4800000000000000000),
            (exactRationalLiteral (-232397031967388793) 400000000000000000),
            (exactRationalLiteral (14272404439744201) 20000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3376561321717524759) 6400000000000000000),
            (exactRationalLiteral (2005752396981649747) 1600000000000000000),
            (exactRationalLiteral (-550509543218786901) 400000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (383657557281926239) 960000000000000000),
            (exactRationalLiteral (-368889016949443627) 400000000000000000),
            (exactRationalLiteral (105675215366480159) 100000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (259528718314473767) 9600000000000000000),
            (exactRationalLiteral (22546584659532651) 160000000000000000),
            (exactRationalLiteral (-54410281960717657) 200000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-565795192130836901) 19200000000000000000),
            (exactRationalLiteral (50770531152490703) 1600000000000000000),
            (exactRationalLiteral (-2586415371805613) 400000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-87554208219437407) 9600000000000000000),
            (exactRationalLiteral (6793100590304817) 800000000000000000),
            (exactRationalLiteral (-247882262377663) 200000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (636024879618349) 9600000000000000000),
            (exactRationalLiteral (3286736597905711) 800000000000000000),
            (exactRationalLiteral (-1688969510063) 8000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-40540486102655941) 9600000000000000000),
            (exactRationalLiteral (441672730666781) 800000000000000000),
            (exactRationalLiteral (-165948319662649) 200000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8713712824864071) 800000000000000000),
            (exactRationalLiteral (-138226387166591) 50000000000000000),
            (exactRationalLiteral (-36723150817887) 50000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (14565663368224753) 9600000000000000000),
            (exactRationalLiteral (1423864925845359) 800000000000000000),
            (exactRationalLiteral (10110646173521) 40000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (46213431489190813) 19200000000000000000),
            (exactRationalLiteral (1008092590549137) 1600000000000000000),
            (exactRationalLiteral (97284902287477) 400000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9954549488143273) 19200000000000000000),
            (exactRationalLiteral (1394093794649921) 1600000000000000000),
            (exactRationalLiteral (-62075963685671) 400000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-23489174051226869) 19200000000000000000),
            (exactRationalLiteral (-3206196481599401) 1600000000000000000),
            (exactRationalLiteral (173540096304403) 400000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2682883763580203) 3200000000000000000),
            (exactRationalLiteral (4424646235471509) 800000000000000000),
            (exactRationalLiteral (-638065544564439) 200000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-161616796093603) 16000000000000000),
            (exactRationalLiteral (-5881449427864173) 200000000000000000),
            (exactRationalLiteral (107366698386279) 12500000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (109340490401234549) 4800000000000000000),
            (exactRationalLiteral (9261501574981743) 80000000000000000),
            (exactRationalLiteral (2599980446377433) 100000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (181250617323517411) 6400000000000000000),
            (exactRationalLiteral (-55113575268516207) 320000000000000000),
            (exactRationalLiteral (-48770024552233743) 400000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-182212317671436161) 2400000000000000000),
            (exactRationalLiteral (32904289378637871) 400000000000000000),
            (exactRationalLiteral (4227089148138149) 25000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (579598786893711043) 19200000000000000000),
            (exactRationalLiteral (27489393991962743) 1600000000000000000),
            (exactRationalLiteral (-40690129848254213) 400000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2745191161656999) 640000000000000000),
            (exactRationalLiteral (-2745191161656999) 160000000000000000),
            (exactRationalLiteral (915063720552333) 40000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (exactRationalLiteral (39356942324172347) 1200000000000000000),
          (exactRationalLiteral (17718321092853791) 200000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (1320247684177261) 300000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (1698580507476641) 150000000000000000),
          (exactRationalLiteral (11322317617059851) 300000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (52745535823769759) 75000000000000000),
          (exactRationalLiteral (70193564788543393) 75000000000000000),
          (exactRationalLiteral (6308541732004091) 18750000000000000),
          (exactRationalLiteral (2669986268059613) 100000000000000000),
          (exactRationalLiteral (68902813403791141) 150000000000000000),
          (exactRationalLiteral (23569805393854899) 25000000000000000),
          (exactRationalLiteral (68902813403791141) 150000000000000000),
          (exactRationalLiteral (2669986268059613) 100000000000000000),
          (exactRationalLiteral (6308541732004091) 18750000000000000),
          (exactRationalLiteral (70193564788543393) 75000000000000000),
          (exactRationalLiteral (52745535823769759) 75000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (11322317617059851) 300000000000000000),
          (exactRationalLiteral (1698580507476641) 150000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (1320247684177261) 300000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (17718321092853791) 200000000000000000),
          (exactRationalLiteral (39356942324172347) 1200000000000000000),
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (44, 55),
      (44, 57)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 5
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
            (exactRationalLiteral (101673746728037) 640000000000000000),
            (exactRationalLiteral (-305021240184111) 160000000000000000),
            (exactRationalLiteral (305021240184111) 40000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (400791461043800521) 19200000000000000000),
            (exactRationalLiteral (-63002191212372321) 1600000000000000000),
            (exactRationalLiteral (-4555662753913319) 400000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3257376204739969) 300000000000000000),
            (exactRationalLiteral (2261120643645419) 16000000000000000),
            (exactRationalLiteral (-2548246618151897) 50000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-413997866905435831) 6400000000000000000),
            (exactRationalLiteral (-244196924553800307) 1600000000000000000),
            (exactRationalLiteral (64455500446624107) 400000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (336155619289138843) 4800000000000000000),
            (exactRationalLiteral (15592587801379851) 400000000000000000),
            (exactRationalLiteral (-3591488096628373) 20000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-935115395819363) 60000000000000000),
            (exactRationalLiteral (4322917059271079) 200000000000000000),
            (exactRationalLiteral (467271645002251) 5000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (9882558296243923) 9600000000000000000),
            (exactRationalLiteral (-6656207879062483) 800000000000000000),
            (exactRationalLiteral (-4902361512702557) 200000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-32311830911515151) 19200000000000000000),
            (exactRationalLiteral (330796868089171) 320000000000000000),
            (exactRationalLiteral (90262012588729) 16000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (14681315697281251) 19200000000000000000),
            (exactRationalLiteral (-300652557359511) 1600000000000000000),
            (exactRationalLiteral (-157059442463809) 80000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (18301888297319149) 6400000000000000000),
            (exactRationalLiteral (2135361715710089) 1600000000000000000),
            (exactRationalLiteral (466349660292999) 400000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (23285021670130079) 9600000000000000000),
            (exactRationalLiteral (282168567505347) 160000000000000000),
            (exactRationalLiteral (-57064275026917) 200000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-29781553408445089) 2400000000000000000),
            (exactRationalLiteral (-40059379247371) 12500000000000000),
            (exactRationalLiteral (-7299108827899) 50000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-1632208657375283) 384000000000000000),
            (exactRationalLiteral (-683813987871331) 800000000000000000),
            (exactRationalLiteral (-396795039606407) 200000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6782404433836121) 3200000000000000000),
            (exactRationalLiteral (673313898127347) 160000000000000000),
            (exactRationalLiteral (82140684117087) 200000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9902845243595809) 1920000000000000000),
            (exactRationalLiteral (5929554344874873) 800000000000000000),
            (exactRationalLiteral (-183890860337309) 200000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-302110623372723119) 19200000000000000000),
            (exactRationalLiteral (35474052817686711) 1600000000000000000),
            (exactRationalLiteral (-5061823795596383) 400000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (148070130539370687) 3200000000000000000),
            (exactRationalLiteral (-24304446022072049) 800000000000000000),
            (exactRationalLiteral (-2821680539829999) 40000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (703185794199835157) 4800000000000000000),
            (exactRationalLiteral (-81123392938971083) 400000000000000000),
            (exactRationalLiteral (38207596638756113) 100000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3332621700982323511) 19200000000000000000),
            (exactRationalLiteral (488045424559399691) 1600000000000000000),
            (exactRationalLiteral (-208343942992338127) 400000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-39401814944885737) 4800000000000000000),
            (exactRationalLiteral (-38092681136914969) 400000000000000000),
            (exactRationalLiteral (25790153216515907) 100000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (23914269397210939) 6400000000000000000),
            (exactRationalLiteral (-9011440076472257) 1600000000000000000),
            (exactRationalLiteral (-11161030019232783) 400000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-5321122956166937723) 19200000000000000000),
            (exactRationalLiteral (271037662623346719) 1600000000000000000),
            (exactRationalLiteral (-5704491673158103) 80000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (74885077364170521) 128000000000000000),
            (exactRationalLiteral (-277983918019830759) 800000000000000000),
            (exactRationalLiteral (5247149289652719) 40000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-5321122956166937723) 19200000000000000000),
            (exactRationalLiteral (271037662623346719) 1600000000000000000),
            (exactRationalLiteral (-5704491673158103) 80000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (23914269397210939) 6400000000000000000),
            (exactRationalLiteral (-9011440076472257) 1600000000000000000),
            (exactRationalLiteral (-11161030019232783) 400000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-39401814944885737) 4800000000000000000),
            (exactRationalLiteral (-38092681136914969) 400000000000000000),
            (exactRationalLiteral (25790153216515907) 100000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3332621700982323511) 19200000000000000000),
            (exactRationalLiteral (488045424559399691) 1600000000000000000),
            (exactRationalLiteral (-208343942992338127) 400000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (703185794199835157) 4800000000000000000),
            (exactRationalLiteral (-81123392938971083) 400000000000000000),
            (exactRationalLiteral (38207596638756113) 100000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (148070130539370687) 3200000000000000000),
            (exactRationalLiteral (-24304446022072049) 800000000000000000),
            (exactRationalLiteral (-2821680539829999) 40000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-302110623372723119) 19200000000000000000),
            (exactRationalLiteral (35474052817686711) 1600000000000000000),
            (exactRationalLiteral (-5061823795596383) 400000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-9902845243595809) 1920000000000000000),
            (exactRationalLiteral (5929554344874873) 800000000000000000),
            (exactRationalLiteral (-183890860337309) 200000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6782404433836121) 3200000000000000000),
            (exactRationalLiteral (673313898127347) 160000000000000000),
            (exactRationalLiteral (82140684117087) 200000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1632208657375283) 384000000000000000),
            (exactRationalLiteral (-683813987871331) 800000000000000000),
            (exactRationalLiteral (-396795039606407) 200000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-29781553408445089) 2400000000000000000),
            (exactRationalLiteral (-40059379247371) 12500000000000000),
            (exactRationalLiteral (-7299108827899) 50000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (23285021670130079) 9600000000000000000),
            (exactRationalLiteral (282168567505347) 160000000000000000),
            (exactRationalLiteral (-57064275026917) 200000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (18301888297319149) 6400000000000000000),
            (exactRationalLiteral (2135361715710089) 1600000000000000000),
            (exactRationalLiteral (466349660292999) 400000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14681315697281251) 19200000000000000000),
            (exactRationalLiteral (-300652557359511) 1600000000000000000),
            (exactRationalLiteral (-157059442463809) 80000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-32311830911515151) 19200000000000000000),
            (exactRationalLiteral (330796868089171) 320000000000000000),
            (exactRationalLiteral (90262012588729) 16000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (9882558296243923) 9600000000000000000),
            (exactRationalLiteral (-6656207879062483) 800000000000000000),
            (exactRationalLiteral (-4902361512702557) 200000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-935115395819363) 60000000000000000),
            (exactRationalLiteral (4322917059271079) 200000000000000000),
            (exactRationalLiteral (467271645002251) 5000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (336155619289138843) 4800000000000000000),
            (exactRationalLiteral (15592587801379851) 400000000000000000),
            (exactRationalLiteral (-3591488096628373) 20000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-413997866905435831) 6400000000000000000),
            (exactRationalLiteral (-244196924553800307) 1600000000000000000),
            (exactRationalLiteral (64455500446624107) 400000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-3257376204739969) 300000000000000000),
            (exactRationalLiteral (2261120643645419) 16000000000000000),
            (exactRationalLiteral (-2548246618151897) 50000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (400791461043800521) 19200000000000000000),
            (exactRationalLiteral (-63002191212372321) 1600000000000000000),
            (exactRationalLiteral (-4555662753913319) 400000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 640000000000000000),
            (exactRationalLiteral (-305021240184111) 160000000000000000),
            (exactRationalLiteral (305021240184111) 40000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (101673746728037) 80000000000000000),
          (exactRationalLiteral (13951595321800177) 480000000000000000),
          (exactRationalLiteral (56497280585932279) 1200000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (23749022377401263) 300000000000000000),
          (exactRationalLiteral (3689885376152451) 200000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (109940188929601) 60000000000000000),
          (exactRationalLiteral (161745531005807) 200000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (31423386248132371) 600000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (548967560876961) 100000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (817167956189846509) 1200000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (548967560876961) 100000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (31423386248132371) 600000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (161745531005807) 200000000000000000),
          (exactRationalLiteral (109940188929601) 60000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (3689885376152451) 200000000000000000),
          (exactRationalLiteral (23749022377401263) 300000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (56497280585932279) 1200000000000000000),
          (exactRationalLiteral (13951595321800177) 480000000000000000),
          (exactRationalLiteral (101673746728037) 80000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (44, 54),
      (44, 56)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 5
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
            (exactRationalLiteral (34874095127716691) 5120000000000000000),
            (exactRationalLiteral (-14946040769021439) 640000000000000000),
            (exactRationalLiteral (2135148681288777) 80000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (4044709554609439703) 153600000000000000000),
            (exactRationalLiteral (290785328908038271) 6400000000000000000),
            (exactRationalLiteral (-99447493243678873) 800000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3197795990816889257) 38400000000000000000),
            (exactRationalLiteral (10596261245982581) 320000000000000000),
            (exactRationalLiteral (44819138099533387) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (2435865474020852967) 51200000000000000000),
            (exactRationalLiteral (-850578644661960243) 6400000000000000000),
            (exactRationalLiteral (-154152811603896411) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (114970807284665353) 12800000000000000000),
            (exactRationalLiteral (164551399249365479) 1600000000000000000),
            (exactRationalLiteral (3095734271502903) 40000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4916303449796861) 768000000000000000),
            (exactRationalLiteral (-23122040057398459) 800000000000000000),
            (exactRationalLiteral (-252538248229693) 20000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (9597210216949189) 76800000000000000000),
            (exactRationalLiteral (18118699136074733) 3200000000000000000),
            (exactRationalLiteral (856016894940181) 400000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-149439299162002633) 153600000000000000000),
            (exactRationalLiteral (-2495488240481661) 1280000000000000000),
            (exactRationalLiteral (-138884983319621) 160000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (62896425211549793) 153600000000000000000),
            (exactRationalLiteral (5463068409025681) 6400000000000000000),
            (exactRationalLiteral (47491739389069) 160000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (358009517861658961) 153600000000000000000),
            (exactRationalLiteral (3827763132049401) 6400000000000000000),
            (exactRationalLiteral (10037425572193) 800000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (33265351991268869) 25600000000000000000),
            (exactRationalLiteral (1087887605392751) 640000000000000000),
            (exactRationalLiteral (154915214682471) 400000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-50682323034660913) 4800000000000000000),
            (exactRationalLiteral (-1025008785199457) 400000000000000000),
            (exactRationalLiteral (-5509895164423) 6250000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-22033615209816861) 5120000000000000000),
            (exactRationalLiteral (2315060841345841) 3200000000000000000),
            (exactRationalLiteral (-216473279353419) 400000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-34668168025365521) 76800000000000000000),
            (exactRationalLiteral (535121032142539) 128000000000000000),
            (exactRationalLiteral (-146630936437481) 400000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-52231344140962881) 5120000000000000000),
            (exactRationalLiteral (28195927111750097) 3200000000000000000),
            (exactRationalLiteral (-527760225775503) 400000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5149888698895521937) 153600000000000000000),
            (exactRationalLiteral (212190081885289879) 6400000000000000000),
            (exactRationalLiteral (-3935126531715841) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (376822035548741303) 76800000000000000000),
            (exactRationalLiteral (688723760664307479) 3200000000000000000),
            (exactRationalLiteral (-25794300710443829) 80000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (20440755596233116061) 38400000000000000000),
            (exactRationalLiteral (-1931990738627557167) 1600000000000000000),
            (exactRationalLiteral (245084240096822341) 200000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-108580640544426336973) 153600000000000000000),
            (exactRationalLiteral (10396130560914970979) 6400000000000000000),
            (exactRationalLiteral (-1272101886550798189) 800000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8687111142521016919) 38400000000000000000),
            (exactRationalLiteral (-1237822151155541741) 1600000000000000000),
            (exactRationalLiteral (165509978888544559) 200000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-2245337307893351369) 153600000000000000000),
            (exactRationalLiteral (524337175104733007) 6400000000000000000),
            (exactRationalLiteral (-89754527043658841) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-21482512418114997683) 51200000000000000000),
            (exactRationalLiteral (1922184836357219351) 6400000000000000000),
            (exactRationalLiteral (-22112384088237093) 160000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13316685038428837853) 15360000000000000000),
            (exactRationalLiteral (-1844246946087093311) 3200000000000000000),
            (exactRationalLiteral (18798152381005373) 80000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-21482512418114997683) 51200000000000000000),
            (exactRationalLiteral (1922184836357219351) 6400000000000000000),
            (exactRationalLiteral (-22112384088237093) 160000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2245337307893351369) 153600000000000000000),
            (exactRationalLiteral (524337175104733007) 6400000000000000000),
            (exactRationalLiteral (-89754527043658841) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (8687111142521016919) 38400000000000000000),
            (exactRationalLiteral (-1237822151155541741) 1600000000000000000),
            (exactRationalLiteral (165509978888544559) 200000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-108580640544426336973) 153600000000000000000),
            (exactRationalLiteral (10396130560914970979) 6400000000000000000),
            (exactRationalLiteral (-1272101886550798189) 800000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (20440755596233116061) 38400000000000000000),
            (exactRationalLiteral (-1931990738627557167) 1600000000000000000),
            (exactRationalLiteral (245084240096822341) 200000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (376822035548741303) 76800000000000000000),
            (exactRationalLiteral (688723760664307479) 3200000000000000000),
            (exactRationalLiteral (-25794300710443829) 80000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5149888698895521937) 153600000000000000000),
            (exactRationalLiteral (212190081885289879) 6400000000000000000),
            (exactRationalLiteral (-3935126531715841) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-52231344140962881) 5120000000000000000),
            (exactRationalLiteral (28195927111750097) 3200000000000000000),
            (exactRationalLiteral (-527760225775503) 400000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-34668168025365521) 76800000000000000000),
            (exactRationalLiteral (535121032142539) 128000000000000000),
            (exactRationalLiteral (-146630936437481) 400000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-22033615209816861) 5120000000000000000),
            (exactRationalLiteral (2315060841345841) 3200000000000000000),
            (exactRationalLiteral (-216473279353419) 400000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-50682323034660913) 4800000000000000000),
            (exactRationalLiteral (-1025008785199457) 400000000000000000),
            (exactRationalLiteral (-5509895164423) 6250000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (33265351991268869) 25600000000000000000),
            (exactRationalLiteral (1087887605392751) 640000000000000000),
            (exactRationalLiteral (154915214682471) 400000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (358009517861658961) 153600000000000000000),
            (exactRationalLiteral (3827763132049401) 6400000000000000000),
            (exactRationalLiteral (10037425572193) 800000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (62896425211549793) 153600000000000000000),
            (exactRationalLiteral (5463068409025681) 6400000000000000000),
            (exactRationalLiteral (47491739389069) 160000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-149439299162002633) 153600000000000000000),
            (exactRationalLiteral (-2495488240481661) 1280000000000000000),
            (exactRationalLiteral (-138884983319621) 160000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (9597210216949189) 76800000000000000000),
            (exactRationalLiteral (18118699136074733) 3200000000000000000),
            (exactRationalLiteral (856016894940181) 400000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4916303449796861) 768000000000000000),
            (exactRationalLiteral (-23122040057398459) 800000000000000000),
            (exactRationalLiteral (-252538248229693) 20000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (114970807284665353) 12800000000000000000),
            (exactRationalLiteral (164551399249365479) 1600000000000000000),
            (exactRationalLiteral (3095734271502903) 40000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2435865474020852967) 51200000000000000000),
            (exactRationalLiteral (-850578644661960243) 6400000000000000000),
            (exactRationalLiteral (-154152811603896411) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-3197795990816889257) 38400000000000000000),
            (exactRationalLiteral (10596261245982581) 320000000000000000),
            (exactRationalLiteral (44819138099533387) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (4044709554609439703) 153600000000000000000),
            (exactRationalLiteral (290785328908038271) 6400000000000000000),
            (exactRationalLiteral (-99447493243678873) 800000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (34874095127716691) 5120000000000000000),
            (exactRationalLiteral (-14946040769021439) 640000000000000000),
            (exactRationalLiteral (2135148681288777) 80000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (exactRationalLiteral (579598786893711043) 19200000000000000000),
          (exactRationalLiteral (103331214376898867) 1200000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (109340490401234549) 4800000000000000000),
          (exactRationalLiteral (161616796093603) 16000000000000000),
          (exactRationalLiteral (2682883763580203) 3200000000000000000),
          (exactRationalLiteral (23489174051226869) 19200000000000000000),
          (exactRationalLiteral (9954549488143273) 19200000000000000000),
          (exactRationalLiteral (46213431489190813) 19200000000000000000),
          (exactRationalLiteral (14565663368224753) 9600000000000000000),
          (exactRationalLiteral (8713712824864071) 800000000000000000),
          (exactRationalLiteral (1320247684177261) 300000000000000000),
          (exactRationalLiteral (19610500183933) 20000000000000000),
          (exactRationalLiteral (1698580507476641) 150000000000000000),
          (exactRationalLiteral (11322317617059851) 300000000000000000),
          (exactRationalLiteral (27297066363693) 1000000000000000),
          (exactRationalLiteral (52745535823769759) 75000000000000000),
          (exactRationalLiteral (70193564788543393) 75000000000000000),
          (exactRationalLiteral (6308541732004091) 18750000000000000),
          (exactRationalLiteral (2669986268059613) 100000000000000000),
          (exactRationalLiteral (68902813403791141) 150000000000000000),
          (exactRationalLiteral (23569805393854899) 25000000000000000),
          (exactRationalLiteral (68902813403791141) 150000000000000000),
          (exactRationalLiteral (2669986268059613) 100000000000000000),
          (exactRationalLiteral (6308541732004091) 18750000000000000),
          (exactRationalLiteral (70193564788543393) 75000000000000000),
          (exactRationalLiteral (52745535823769759) 75000000000000000),
          (exactRationalLiteral (27297066363693) 1000000000000000),
          (exactRationalLiteral (11322317617059851) 300000000000000000),
          (exactRationalLiteral (1698580507476641) 150000000000000000),
          (exactRationalLiteral (19610500183933) 20000000000000000),
          (exactRationalLiteral (1320247684177261) 300000000000000000),
          (exactRationalLiteral (8713712824864071) 800000000000000000),
          (exactRationalLiteral (14565663368224753) 9600000000000000000),
          (exactRationalLiteral (46213431489190813) 19200000000000000000),
          (exactRationalLiteral (9954549488143273) 19200000000000000000),
          (exactRationalLiteral (23489174051226869) 19200000000000000000),
          (exactRationalLiteral (2682883763580203) 3200000000000000000),
          (exactRationalLiteral (161616796093603) 16000000000000000),
          (exactRationalLiteral (109340490401234549) 4800000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (103331214376898867) 1200000000000000000),
          (exactRationalLiteral (579598786893711043) 19200000000000000000),
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (42, 21),
      (42, 25)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
        cell := 5
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
            (exactRationalLiteral (101673746728037) 40960000000000000),
            (exactRationalLiteral (-305021240184111) 25600000000000000),
            (exactRationalLiteral (305021240184111) 16000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (4740589477510886429) 153600000000000000000),
            (exactRationalLiteral (-34735709877995433) 6400000000000000000),
            (exactRationalLiteral (-63313026149337979) 800000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2430097895558436743) 38400000000000000000),
            (exactRationalLiteral (188248158970333673) 1600000000000000000),
            (exactRationalLiteral (22814288270676997) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (269064304946490637) 51200000000000000000),
            (exactRationalLiteral (-1240738841079830187) 6400000000000000000),
            (exactRationalLiteral (-40927286605038561) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (1435735189922285921) 38400000000000000000),
            (exactRationalLiteral (185351242820384943) 1600000000000000000),
            (exactRationalLiteral (-5078749572004783) 200000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-259819122857184283) 19200000000000000000),
            (exactRationalLiteral (-19686305709037531) 800000000000000000),
            (exactRationalLiteral (2980558415328929) 100000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (111524423900127287) 76800000000000000000),
            (exactRationalLiteral (13014174779559221) 3200000000000000000),
            (exactRationalLiteral (-3408279073197937) 400000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-44861000900394887) 30720000000000000000),
            (exactRationalLiteral (-11089120431973081) 6400000000000000000),
            (exactRationalLiteral (1388585301815717) 800000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (95631455034514523) 153600000000000000000),
            (exactRationalLiteral (4966460699540313) 6400000000000000000),
            (exactRationalLiteral (-485762551688029) 800000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (127524268264281257) 51200000000000000000),
            (exactRationalLiteral (4606042350349217) 6400000000000000000),
            (exactRationalLiteral (75820436715543) 160000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (133861196688200701) 76800000000000000000),
            (exactRationalLiteral (1168772774780919) 640000000000000000),
            (exactRationalLiteral (47297708787949) 400000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33745250197601) 3000000000000000),
            (exactRationalLiteral (-234380277694201) 80000000000000000),
            (exactRationalLiteral (-2936714032039) 5000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-320134929331193929) 76800000000000000000),
            (exactRationalLiteral (987474284044649) 3200000000000000000),
            (exactRationalLiteral (-447319999297177) 400000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2955858349749347) 5120000000000000000),
            (exactRationalLiteral (104321855212407) 25600000000000000),
            (exactRationalLiteral (-22266014568819) 400000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-620371756545087253) 76800000000000000000),
            (exactRationalLiteral (26212869012728793) 3200000000000000000),
            (exactRationalLiteral (-463768823735149) 400000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-786774271931907167) 30720000000000000000),
            (exactRationalLiteral (7659950356433799) 256000000000000000),
            (exactRationalLiteral (-6410534955506611) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (208180938263615139) 5120000000000000000),
            (exactRationalLiteral (253441504978566223) 3200000000000000000),
            (exactRationalLiteral (-88669624290651483) 400000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (11519951570718744967) 38400000000000000000),
            (exactRationalLiteral (-217317803139143179) 320000000000000000),
            (exactRationalLiteral (35523324273819659) 40000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-60100417416640294271) 153600000000000000000),
            (exactRationalLiteral (5992054215164675771) 6400000000000000000),
            (exactRationalLiteral (-185987257264869883) 160000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3064010506321480789) 38400000000000000000),
            (exactRationalLiteral (-666925973565773701) 1600000000000000000),
            (exactRationalLiteral (119938109906339461) 200000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-22825544860183393) 51200000000000000000),
            (exactRationalLiteral (219265040534252263) 6400000000000000000),
            (exactRationalLiteral (-62781540241581531) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-54155544075560535427) 153600000000000000000),
            (exactRationalLiteral (1522750757560161039) 6400000000000000000),
            (exactRationalLiteral (-89155118957343691) 800000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (18859800609356117433) 25600000000000000000),
            (exactRationalLiteral (-1501499313673785591) 3200000000000000000),
            (exactRationalLiteral (15476610860325399) 80000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-54155544075560535427) 153600000000000000000),
            (exactRationalLiteral (1522750757560161039) 6400000000000000000),
            (exactRationalLiteral (-89155118957343691) 800000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22825544860183393) 51200000000000000000),
            (exactRationalLiteral (219265040534252263) 6400000000000000000),
            (exactRationalLiteral (-62781540241581531) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (3064010506321480789) 38400000000000000000),
            (exactRationalLiteral (-666925973565773701) 1600000000000000000),
            (exactRationalLiteral (119938109906339461) 200000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-60100417416640294271) 153600000000000000000),
            (exactRationalLiteral (5992054215164675771) 6400000000000000000),
            (exactRationalLiteral (-185987257264869883) 160000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11519951570718744967) 38400000000000000000),
            (exactRationalLiteral (-217317803139143179) 320000000000000000),
            (exactRationalLiteral (35523324273819659) 40000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (208180938263615139) 5120000000000000000),
            (exactRationalLiteral (253441504978566223) 3200000000000000000),
            (exactRationalLiteral (-88669624290651483) 400000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-786774271931907167) 30720000000000000000),
            (exactRationalLiteral (7659950356433799) 256000000000000000),
            (exactRationalLiteral (-6410534955506611) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-620371756545087253) 76800000000000000000),
            (exactRationalLiteral (26212869012728793) 3200000000000000000),
            (exactRationalLiteral (-463768823735149) 400000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2955858349749347) 5120000000000000000),
            (exactRationalLiteral (104321855212407) 25600000000000000),
            (exactRationalLiteral (-22266014568819) 400000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-320134929331193929) 76800000000000000000),
            (exactRationalLiteral (987474284044649) 3200000000000000000),
            (exactRationalLiteral (-447319999297177) 400000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33745250197601) 3000000000000000),
            (exactRationalLiteral (-234380277694201) 80000000000000000),
            (exactRationalLiteral (-2936714032039) 5000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (133861196688200701) 76800000000000000000),
            (exactRationalLiteral (1168772774780919) 640000000000000000),
            (exactRationalLiteral (47297708787949) 400000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (127524268264281257) 51200000000000000000),
            (exactRationalLiteral (4606042350349217) 6400000000000000000),
            (exactRationalLiteral (75820436715543) 160000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (95631455034514523) 153600000000000000000),
            (exactRationalLiteral (4966460699540313) 6400000000000000000),
            (exactRationalLiteral (-485762551688029) 800000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-44861000900394887) 30720000000000000000),
            (exactRationalLiteral (-11089120431973081) 6400000000000000000),
            (exactRationalLiteral (1388585301815717) 800000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (111524423900127287) 76800000000000000000),
            (exactRationalLiteral (13014174779559221) 3200000000000000000),
            (exactRationalLiteral (-3408279073197937) 400000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-259819122857184283) 19200000000000000000),
            (exactRationalLiteral (-19686305709037531) 800000000000000000),
            (exactRationalLiteral (2980558415328929) 100000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1435735189922285921) 38400000000000000000),
            (exactRationalLiteral (185351242820384943) 1600000000000000000),
            (exactRationalLiteral (-5078749572004783) 200000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (269064304946490637) 51200000000000000000),
            (exactRationalLiteral (-1240738841079830187) 6400000000000000000),
            (exactRationalLiteral (-40927286605038561) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-2430097895558436743) 38400000000000000000),
            (exactRationalLiteral (188248158970333673) 1600000000000000000),
            (exactRationalLiteral (22814288270676997) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (4740589477510886429) 153600000000000000000),
            (exactRationalLiteral (-34735709877995433) 6400000000000000000),
            (exactRationalLiteral (-63313026149337979) 800000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 40960000000000000),
            (exactRationalLiteral (-305021240184111) 25600000000000000),
            (exactRationalLiteral (305021240184111) 16000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (exactRationalLiteral (2745191161656999) 640000000000000000),
          (exactRationalLiteral (101181363480945631) 3200000000000000000),
          (exactRationalLiteral (182212317671436161) 2400000000000000000),
          (exactRationalLiteral (181250617323517411) 6400000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (40540486102655941) 9600000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (87554208219437407) 9600000000000000000),
          (exactRationalLiteral (565795192130836901) 19200000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (383657557281926239) 960000000000000000),
          (exactRationalLiteral (3376561321717524759) 6400000000000000000),
          (exactRationalLiteral (680923586403615353) 4800000000000000000),
          (exactRationalLiteral (116012858788636277) 19200000000000000000),
          (exactRationalLiteral (7375245638231871313) 19200000000000000000),
          (exactRationalLiteral (7665544098224536249) 9600000000000000000),
          (exactRationalLiteral (7375245638231871313) 19200000000000000000),
          (exactRationalLiteral (116012858788636277) 19200000000000000000),
          (exactRationalLiteral (680923586403615353) 4800000000000000000),
          (exactRationalLiteral (3376561321717524759) 6400000000000000000),
          (exactRationalLiteral (383657557281926239) 960000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (565795192130836901) 19200000000000000000),
          (exactRationalLiteral (87554208219437407) 9600000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (40540486102655941) 9600000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (181250617323517411) 6400000000000000000),
          (exactRationalLiteral (182212317671436161) 2400000000000000000),
          (exactRationalLiteral (101181363480945631) 3200000000000000000),
          (exactRationalLiteral (2745191161656999) 640000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (42, 20),
      (42, 24)
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
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
      true,
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
theorem generatorCoordinates21_valid : ∀ i, (generatorCoordinates21 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
