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

/-- Actual coordinate interval candidates, block 31. -/
def generatorCoordinates31 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 7
        lower := (exactRationalLiteral (1) 8)
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
            (exactRationalLiteral (23835348560526530013) 3276800000000000000000),
            (exactRationalLiteral (-2648372062280725557) 102400000000000000000),
            (exactRationalLiteral (98087854158545391) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14452503083006250853) 491520000000000000000),
            (exactRationalLiteral (241232951907192409) 5120000000000000000),
            (exactRationalLiteral (-22095754517906339) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-151398860385355185387) 1638400000000000000000),
            (exactRationalLiteral (2273318410327111699) 51200000000000000000),
            (exactRationalLiteral (383434453910059863) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (165817315376803557323) 3276800000000000000000),
            (exactRationalLiteral (-3129403720716753559) 20480000000000000000),
            (exactRationalLiteral (-626655567984059319) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (40400879507388870653) 3276800000000000000000),
            (exactRationalLiteral (11630452920999470027) 102400000000000000000),
            (exactRationalLiteral (228265181067993231) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1574446605034121651) 204800000000000000000),
            (exactRationalLiteral (-199157083168075113) 6400000000000000000),
            (exactRationalLiteral (-1753930291581609) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (2309987412743679997) 1638400000000000000000),
            (exactRationalLiteral (356259050422437963) 51200000000000000000),
            (exactRationalLiteral (543619293003651) 320000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (26289935431167359731) 4915200000000000000000),
            (exactRationalLiteral (-299651972291009) 2048000000000000000),
            (exactRationalLiteral (-1292224674876533) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (627051924273965143) 98304000000000000000),
            (exactRationalLiteral (167080800510640123) 25600000000000000000),
            (exactRationalLiteral (2957993065639591) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-31278261372325103921) 1638400000000000000000),
            (exactRationalLiteral (-446464909736760999) 51200000000000000000),
            (exactRationalLiteral (-4869986798254827) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33979180768649643061) 3276800000000000000000),
            (exactRationalLiteral (-864586459217591667) 102400000000000000000),
            (exactRationalLiteral (-18209579785890999) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (58835078025137172661) 4915200000000000000000),
            (exactRationalLiteral (132377286342883789) 10240000000000000000),
            (exactRationalLiteral (10512678572150941) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (501572081092159927) 1966080000000000000000),
            (exactRationalLiteral (-329838956073957641) 102400000000000000000),
            (exactRationalLiteral (-15424661811839989) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-18551909428575523321) 4915200000000000000000),
            (exactRationalLiteral (316072888106907851) 51200000000000000000),
            (exactRationalLiteral (1008291841212211) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (71474873428844047843) 4915200000000000000000),
            (exactRationalLiteral (-508189911819320953) 51200000000000000000),
            (exactRationalLiteral (1187184821601499) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (228088109097278612191) 4915200000000000000000),
            (exactRationalLiteral (-317472712746074921) 10240000000000000000),
            (exactRationalLiteral (4492680959763659) 320000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-107192263368985956451) 3276800000000000000000),
            (exactRationalLiteral (3316570784899408331) 102400000000000000000),
            (exactRationalLiteral (-11388852097542621) 640000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-73772477121846748557) 3276800000000000000000),
            (exactRationalLiteral (766062649014850981) 102400000000000000000),
            (exactRationalLiteral (666625321956609) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-853885723566823247) 163840000000000000000),
            (exactRationalLiteral (-6510511268838281) 5120000000000000000),
            (exactRationalLiteral (440867513653131) 160000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-51256934319558874501) 409600000000000000000),
            (exactRationalLiteral (833197406938842929) 12800000000000000000),
            (exactRationalLiteral (-8672051700048159) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1307311656038284378993) 4915200000000000000000),
            (exactRationalLiteral (-7181162405343160707) 51200000000000000000),
            (exactRationalLiteral (70529343008047897) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-51256934319558874501) 409600000000000000000),
            (exactRationalLiteral (833197406938842929) 12800000000000000000),
            (exactRationalLiteral (-8672051700048159) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-853885723566823247) 163840000000000000000),
            (exactRationalLiteral (-6510511268838281) 5120000000000000000),
            (exactRationalLiteral (440867513653131) 160000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-73772477121846748557) 3276800000000000000000),
            (exactRationalLiteral (766062649014850981) 102400000000000000000),
            (exactRationalLiteral (666625321956609) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-107192263368985956451) 3276800000000000000000),
            (exactRationalLiteral (3316570784899408331) 102400000000000000000),
            (exactRationalLiteral (-11388852097542621) 640000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (228088109097278612191) 4915200000000000000000),
            (exactRationalLiteral (-317472712746074921) 10240000000000000000),
            (exactRationalLiteral (4492680959763659) 320000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (71474873428844047843) 4915200000000000000000),
            (exactRationalLiteral (-508189911819320953) 51200000000000000000),
            (exactRationalLiteral (1187184821601499) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-18551909428575523321) 4915200000000000000000),
            (exactRationalLiteral (316072888106907851) 51200000000000000000),
            (exactRationalLiteral (1008291841212211) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (501572081092159927) 1966080000000000000000),
            (exactRationalLiteral (-329838956073957641) 102400000000000000000),
            (exactRationalLiteral (-15424661811839989) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (58835078025137172661) 4915200000000000000000),
            (exactRationalLiteral (132377286342883789) 10240000000000000000),
            (exactRationalLiteral (10512678572150941) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-33979180768649643061) 3276800000000000000000),
            (exactRationalLiteral (-864586459217591667) 102400000000000000000),
            (exactRationalLiteral (-18209579785890999) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-31278261372325103921) 1638400000000000000000),
            (exactRationalLiteral (-446464909736760999) 51200000000000000000),
            (exactRationalLiteral (-4869986798254827) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (627051924273965143) 98304000000000000000),
            (exactRationalLiteral (167080800510640123) 25600000000000000000),
            (exactRationalLiteral (2957993065639591) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (26289935431167359731) 4915200000000000000000),
            (exactRationalLiteral (-299651972291009) 2048000000000000000),
            (exactRationalLiteral (-1292224674876533) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2309987412743679997) 1638400000000000000000),
            (exactRationalLiteral (356259050422437963) 51200000000000000000),
            (exactRationalLiteral (543619293003651) 320000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1574446605034121651) 204800000000000000000),
            (exactRationalLiteral (-199157083168075113) 6400000000000000000),
            (exactRationalLiteral (-1753930291581609) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (40400879507388870653) 3276800000000000000000),
            (exactRationalLiteral (11630452920999470027) 102400000000000000000),
            (exactRationalLiteral (228265181067993231) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (165817315376803557323) 3276800000000000000000),
            (exactRationalLiteral (-3129403720716753559) 20480000000000000000),
            (exactRationalLiteral (-626655567984059319) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-151398860385355185387) 1638400000000000000000),
            (exactRationalLiteral (2273318410327111699) 51200000000000000000),
            (exactRationalLiteral (383434453910059863) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (14452503083006250853) 491520000000000000000),
            (exactRationalLiteral (241232951907192409) 5120000000000000000),
            (exactRationalLiteral (-22095754517906339) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (23835348560526530013) 3276800000000000000000),
            (exactRationalLiteral (-2648372062280725557) 102400000000000000000),
            (exactRationalLiteral (98087854158545391) 3200000000000000000),
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
          (exactRationalLiteral (1888869513456449191) 61440000000000000000),
          (exactRationalLiteral (2395008733124649903) 25600000000000000000),
          (exactRationalLiteral (8475809523319801709) 153600000000000000000),
          (exactRationalLiteral (19591926874981109329) 1228800000000000000000),
          (exactRationalLiteral (665619177706774453) 76800000000000000000),
          (exactRationalLiteral (333516886475202139) 204800000000000000000),
          (exactRationalLiteral (411058946573788931) 76800000000000000000),
          (exactRationalLiteral (674430048725156391) 102400000000000000000),
          (exactRationalLiteral (11898540856091107901) 614400000000000000000),
          (exactRationalLiteral (13073488839101703961) 1228800000000000000000),
          (exactRationalLiteral (7606565870125229627) 614400000000000000000),
          (exactRationalLiteral (53896441988318303) 153600000000000000000),
          (exactRationalLiteral (101480479239090587) 25600000000000000000),
          (exactRationalLiteral (228133828239823811) 15360000000000000000),
          (exactRationalLiteral (727869143953301687) 15360000000000000000),
          (exactRationalLiteral (5182793591161372501) 153600000000000000000),
          (exactRationalLiteral (3493959246977188859) 153600000000000000000),
          (exactRationalLiteral (1612424143267127543) 307200000000000000000),
          (exactRationalLiteral (244213395546034837) 1920000000000000000),
          (exactRationalLiteral (6922229041946495767) 25600000000000000000),
          (exactRationalLiteral (244213395546034837) 1920000000000000000),
          (exactRationalLiteral (1612424143267127543) 307200000000000000000),
          (exactRationalLiteral (3493959246977188859) 153600000000000000000),
          (exactRationalLiteral (5182793591161372501) 153600000000000000000),
          (exactRationalLiteral (727869143953301687) 15360000000000000000),
          (exactRationalLiteral (228133828239823811) 15360000000000000000),
          (exactRationalLiteral (101480479239090587) 25600000000000000000),
          (exactRationalLiteral (53896441988318303) 153600000000000000000),
          (exactRationalLiteral (7606565870125229627) 614400000000000000000),
          (exactRationalLiteral (13073488839101703961) 1228800000000000000000),
          (exactRationalLiteral (11898540856091107901) 614400000000000000000),
          (exactRationalLiteral (674430048725156391) 102400000000000000000),
          (exactRationalLiteral (411058946573788931) 76800000000000000000),
          (exactRationalLiteral (333516886475202139) 204800000000000000000),
          (exactRationalLiteral (665619177706774453) 76800000000000000000),
          (exactRationalLiteral (19591926874981109329) 1228800000000000000000),
          (exactRationalLiteral (8475809523319801709) 153600000000000000000),
          (exactRationalLiteral (2395008733124649903) 25600000000000000000),
          (exactRationalLiteral (1888869513456449191) 61440000000000000000),
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
      (31, 34),
      (31, 18),
      (31, 2),
      (30, 50),
      (30, 34),
      (30, 18),
      (30, 2),
      (29, 50),
      (29, 34),
      (29, 18),
      (29, 2),
      (28, 50),
      (28, 34),
      (28, 18),
      (28, 2),
      (27, 50),
      (27, 34),
      (27, 18),
      (27, 2),
      (26, 50),
      (26, 34),
      (26, 18),
      (26, 2),
      (25, 50),
      (25, 34),
      (25, 18),
      (25, 2),
      (24, 50),
      (24, 34),
      (24, 18),
      (24, 2),
      (23, 50),
      (23, 34),
      (23, 18),
      (23, 29),
      (23, 45),
      (23, 61),
      (24, 13),
      (24, 29),
      (24, 45),
      (24, 61),
      (25, 13),
      (25, 29),
      (25, 45),
      (25, 61),
      (26, 13),
      (26, 29),
      (26, 45),
      (26, 61),
      (27, 13),
      (27, 29),
      (27, 45),
      (27, 61)
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
        lower := (exactRationalLiteral (3) 16)
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
            (exactRationalLiteral (3632883487353533) 629145600000000000),
            (exactRationalLiteral (-3632883487353533) 163840000000000000),
            (exactRationalLiteral (3632883487353533) 128000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5214361066684801653) 163840000000000000000),
            (exactRationalLiteral (157015663745504913) 5120000000000000000),
            (exactRationalLiteral (-20012889562937409) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-29076793824683573997) 327680000000000000000),
            (exactRationalLiteral (3708831164431629979) 51200000000000000000),
            (exactRationalLiteral (334321923142199277) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (396539773651039257539) 9830400000000000000000),
            (exactRationalLiteral (-17908737896550052987) 102400000000000000000),
            (exactRationalLiteral (-504204078499083277) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (38675503118563666817) 1966080000000000000000),
            (exactRationalLiteral (12370002331190934547) 102400000000000000000),
            (exactRationalLiteral (141509524027739029) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5930374006992678979) 614400000000000000000),
            (exactRationalLiteral (-201695069025843569) 6400000000000000000),
            (exactRationalLiteral (484937362697381) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (3026742156812476119) 1638400000000000000000),
            (exactRationalLiteral (357177822328281747) 51200000000000000000),
            (exactRationalLiteral (-2258710512096363) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (26235561533961703769) 4915200000000000000000),
            (exactRationalLiteral (-1923980127704893) 10240000000000000000),
            (exactRationalLiteral (227924009251913) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (16713532281306929741) 2457600000000000000000),
            (exactRationalLiteral (35707900015268231) 5120000000000000000),
            (exactRationalLiteral (110854268688437) 32000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-96568317754162967417) 4915200000000000000000),
            (exactRationalLiteral (-18563881020951847) 2048000000000000000),
            (exactRationalLiteral (-3946071095262761) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-107359418337519207229) 9830400000000000000000),
            (exactRationalLiteral (-945345937778173691) 102400000000000000000),
            (exactRationalLiteral (-22170159494400013) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (62934561598329135199) 4915200000000000000000),
            (exactRationalLiteral (704943566022841497) 51200000000000000000),
            (exactRationalLiteral (2203177716412067) 320000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (357578735233223513) 9830400000000000000000),
            (exactRationalLiteral (-384613599342192801) 102400000000000000000),
            (exactRationalLiteral (-11962659822277591) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1106732546696180773) 327680000000000000000),
            (exactRationalLiteral (333231919440468051) 51200000000000000000),
            (exactRationalLiteral (707611292143809) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (13688283526394581109) 983040000000000000000),
            (exactRationalLiteral (-502722444440132241) 51200000000000000000),
            (exactRationalLiteral (1546548867992857) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (218829200074959392509) 4915200000000000000000),
            (exactRationalLiteral (-1499654193296497221) 51200000000000000000),
            (exactRationalLiteral (21391280418120397) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-302349059793745125403) 9830400000000000000000),
            (exactRationalLiteral (3094612107782981523) 102400000000000000000),
            (exactRationalLiteral (-54035078070500299) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-43342975401643678993) 1966080000000000000000),
            (exactRationalLiteral (767818629987310173) 102400000000000000000),
            (exactRationalLiteral (211365164272987) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12977650231203464387) 2457600000000000000000),
            (exactRationalLiteral (-23985751298706341) 25600000000000000000),
            (exactRationalLiteral (2079064954476877) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-148874388618492152533) 1228800000000000000000),
            (exactRationalLiteral (159831291922929189) 2560000000000000000),
            (exactRationalLiteral (-8348421962050333) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (421687025186402843281) 1638400000000000000000),
            (exactRationalLiteral (-1380804822973539791) 10240000000000000000),
            (exactRationalLiteral (68039802229682979) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-148874388618492152533) 1228800000000000000000),
            (exactRationalLiteral (159831291922929189) 2560000000000000000),
            (exactRationalLiteral (-8348421962050333) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12977650231203464387) 2457600000000000000000),
            (exactRationalLiteral (-23985751298706341) 25600000000000000000),
            (exactRationalLiteral (2079064954476877) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-43342975401643678993) 1966080000000000000000),
            (exactRationalLiteral (767818629987310173) 102400000000000000000),
            (exactRationalLiteral (211365164272987) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-302349059793745125403) 9830400000000000000000),
            (exactRationalLiteral (3094612107782981523) 102400000000000000000),
            (exactRationalLiteral (-54035078070500299) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (218829200074959392509) 4915200000000000000000),
            (exactRationalLiteral (-1499654193296497221) 51200000000000000000),
            (exactRationalLiteral (21391280418120397) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (13688283526394581109) 983040000000000000000),
            (exactRationalLiteral (-502722444440132241) 51200000000000000000),
            (exactRationalLiteral (1546548867992857) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1106732546696180773) 327680000000000000000),
            (exactRationalLiteral (333231919440468051) 51200000000000000000),
            (exactRationalLiteral (707611292143809) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (357578735233223513) 9830400000000000000000),
            (exactRationalLiteral (-384613599342192801) 102400000000000000000),
            (exactRationalLiteral (-11962659822277591) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (62934561598329135199) 4915200000000000000000),
            (exactRationalLiteral (704943566022841497) 51200000000000000000),
            (exactRationalLiteral (2203177716412067) 320000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-107359418337519207229) 9830400000000000000000),
            (exactRationalLiteral (-945345937778173691) 102400000000000000000),
            (exactRationalLiteral (-22170159494400013) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-96568317754162967417) 4915200000000000000000),
            (exactRationalLiteral (-18563881020951847) 2048000000000000000),
            (exactRationalLiteral (-3946071095262761) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (16713532281306929741) 2457600000000000000000),
            (exactRationalLiteral (35707900015268231) 5120000000000000000),
            (exactRationalLiteral (110854268688437) 32000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (26235561533961703769) 4915200000000000000000),
            (exactRationalLiteral (-1923980127704893) 10240000000000000000),
            (exactRationalLiteral (227924009251913) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3026742156812476119) 1638400000000000000000),
            (exactRationalLiteral (357177822328281747) 51200000000000000000),
            (exactRationalLiteral (-2258710512096363) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-5930374006992678979) 614400000000000000000),
            (exactRationalLiteral (-201695069025843569) 6400000000000000000),
            (exactRationalLiteral (484937362697381) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (38675503118563666817) 1966080000000000000000),
            (exactRationalLiteral (12370002331190934547) 102400000000000000000),
            (exactRationalLiteral (141509524027739029) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (396539773651039257539) 9830400000000000000000),
            (exactRationalLiteral (-17908737896550052987) 102400000000000000000),
            (exactRationalLiteral (-504204078499083277) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-29076793824683573997) 327680000000000000000),
            (exactRationalLiteral (3708831164431629979) 51200000000000000000),
            (exactRationalLiteral (334321923142199277) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (5214361066684801653) 163840000000000000000),
            (exactRationalLiteral (157015663745504913) 5120000000000000000),
            (exactRationalLiteral (-20012889562937409) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 629145600000000000),
            (exactRationalLiteral (-3632883487353533) 163840000000000000),
            (exactRationalLiteral (3632883487353533) 128000000000000000),
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
          (exactRationalLiteral (7981445021715712001) 1228800000000000000000),
          (exactRationalLiteral (7839420388222457) 240000000000000000),
          (exactRationalLiteral (18593786617864082157) 204800000000000000000),
          (exactRationalLiteral (56086518670056209831) 1228800000000000000000),
          (exactRationalLiteral (150305125865855617) 6400000000000000000),
          (exactRationalLiteral (8506360635618461) 800000000000000000),
          (exactRationalLiteral (264127484437433) 128000000000000000),
          (exactRationalLiteral (218869541113024739) 40960000000000000000),
          (exactRationalLiteral (4213225472049163) 600000000000000000),
          (exactRationalLiteral (63783844457141047) 3200000000000000000),
          (exactRationalLiteral (71786423775515093) 6400000000000000000),
          (exactRationalLiteral (127114631967087491) 9600000000000000000),
          (exactRationalLiteral (184225069099773493) 1228800000000000000000),
          (exactRationalLiteral (2198664761001160951) 614400000000000000000),
          (exactRationalLiteral (1748851123246852129) 122880000000000000000),
          (exactRationalLiteral (27924109069786699289) 614400000000000000000),
          (exactRationalLiteral (38974556992814272159) 1228800000000000000000),
          (exactRationalLiteral (27377183896576083089) 1228800000000000000000),
          (exactRationalLiteral (8491818311551463) 1600000000000000000),
          (exactRationalLiteral (3782426626952281007) 30720000000000000000),
          (exactRationalLiteral (160747314010111232263) 614400000000000000000),
          (exactRationalLiteral (3782426626952281007) 30720000000000000000),
          (exactRationalLiteral (8491818311551463) 1600000000000000000),
          (exactRationalLiteral (27377183896576083089) 1228800000000000000000),
          (exactRationalLiteral (38974556992814272159) 1228800000000000000000),
          (exactRationalLiteral (27924109069786699289) 614400000000000000000),
          (exactRationalLiteral (1748851123246852129) 122880000000000000000),
          (exactRationalLiteral (2198664761001160951) 614400000000000000000),
          (exactRationalLiteral (184225069099773493) 1228800000000000000000),
          (exactRationalLiteral (127114631967087491) 9600000000000000000),
          (exactRationalLiteral (71786423775515093) 6400000000000000000),
          (exactRationalLiteral (63783844457141047) 3200000000000000000),
          (exactRationalLiteral (4213225472049163) 600000000000000000),
          (exactRationalLiteral (218869541113024739) 40960000000000000000),
          (exactRationalLiteral (264127484437433) 128000000000000000),
          (exactRationalLiteral (8506360635618461) 800000000000000000),
          (exactRationalLiteral (150305125865855617) 6400000000000000000),
          (exactRationalLiteral (56086518670056209831) 1228800000000000000000),
          (exactRationalLiteral (18593786617864082157) 204800000000000000000),
          (exactRationalLiteral (7839420388222457) 240000000000000000),
          (exactRationalLiteral (7981445021715712001) 1228800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 35),
      (31, 19),
      (31, 3),
      (30, 51),
      (30, 35),
      (30, 19),
      (30, 3),
      (29, 51),
      (29, 35),
      (29, 19),
      (29, 3),
      (28, 51),
      (28, 35),
      (28, 19),
      (28, 3),
      (27, 51),
      (27, 35),
      (27, 19),
      (27, 3),
      (26, 51),
      (26, 35),
      (26, 19),
      (26, 3),
      (25, 51),
      (25, 35),
      (25, 19),
      (25, 3),
      (24, 51),
      (24, 35),
      (24, 19),
      (24, 3),
      (23, 51),
      (23, 35),
      (23, 19),
      (23, 28),
      (23, 44),
      (23, 60),
      (24, 12),
      (24, 28),
      (24, 44),
      (24, 60),
      (25, 12),
      (25, 28),
      (25, 44),
      (25, 60),
      (26, 12),
      (26, 28),
      (26, 44),
      (26, 60),
      (27, 12),
      (27, 28),
      (27, 44),
      (27, 60)
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
            (exactRationalLiteral (44201293390630436011) 9830400000000000000000),
            (exactRationalLiteral (-1921795364810018957) 102400000000000000000),
            (exactRationalLiteral (83556320209131259) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16353353967592061249) 491520000000000000000),
            (exactRationalLiteral (81129835403693137) 5120000000000000000),
            (exactRationalLiteral (-17930024607968479) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-136694502476342960367) 1638400000000000000000),
            (exactRationalLiteral (989578759092941183) 10240000000000000000),
            (exactRationalLiteral (285209392374338691) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (283526703287689844461) 9830400000000000000000),
            (exactRationalLiteral (-19680651231576434011) 102400000000000000000),
            (exactRationalLiteral (-76350517802821447) 640000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (268948621240135792907) 9830400000000000000000),
            (exactRationalLiteral (12762529113221382259) 102400000000000000000),
            (exactRationalLiteral (54753866987484827) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7125769702178255861) 614400000000000000000),
            (exactRationalLiteral (-39055516853299213) 1280000000000000000),
            (exactRationalLiteral (2723805016976371) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (3725427216784501337) 1638400000000000000000),
            (exactRationalLiteral (338189366325667059) 51200000000000000000),
            (exactRationalLiteral (-7235517489210981) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8728885937659364573) 1638400000000000000000),
            (exactRationalLiteral (-5667907233259921) 51200000000000000000),
            (exactRationalLiteral (1748072693380359) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5939093005659264369) 819200000000000000000),
            (exactRationalLiteral (189251654248327523) 25600000000000000000),
            (exactRationalLiteral (2584720368782259) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-19879311419527385867) 983040000000000000000),
            (exactRationalLiteral (-478033478498863087) 51200000000000000000),
            (exactRationalLiteral (-604431078454139) 320000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-113313378196955085587) 9830400000000000000000),
            (exactRationalLiteral (-1041947735172791771) 102400000000000000000),
            (exactRationalLiteral (-26130739202909027) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (67298426497490545777) 4915200000000000000000),
            (exactRationalLiteral (6000108322967213) 409600000000000000),
            (exactRationalLiteral (11519098591969729) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2079806770729014793) 9830400000000000000000),
            (exactRationalLiteral (-425540234652178369) 102400000000000000000),
            (exactRationalLiteral (-8500657832715193) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-14565153617252642789) 4915200000000000000000),
            (exactRationalLiteral (344377339792660211) 51200000000000000000),
            (exactRationalLiteral (406930743075407) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (13089015801586718363) 983040000000000000000),
            (exactRationalLiteral (-495817520875378097) 51200000000000000000),
            (exactRationalLiteral (381182582876843) 320000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (42016736356535012471) 983040000000000000000),
            (exactRationalLiteral (-1416233320385411429) 51200000000000000000),
            (exactRationalLiteral (20319156037422499) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-284418171354224388629) 9830400000000000000000),
            (exactRationalLiteral (2884290160335405939) 102400000000000000000),
            (exactRationalLiteral (-51125895653287493) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-212107249886953992571) 9830400000000000000000),
            (exactRationalLiteral (767753570329034877) 102400000000000000000),
            (exactRationalLiteral (-48778998682127) 640000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13097117049997135021) 2457600000000000000000),
            (exactRationalLiteral (-15920036708376389) 25600000000000000000),
            (exactRationalLiteral (1953792340688099) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-28835667281079377911) 245760000000000000000),
            (exactRationalLiteral (153282006248488053) 2560000000000000000),
            (exactRationalLiteral (-8024792224052507) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1224443450333645072189) 4915200000000000000000),
            (exactRationalLiteral (-2123790076001823) 16384000000000000),
            (exactRationalLiteral (65550261451318061) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-28835667281079377911) 245760000000000000000),
            (exactRationalLiteral (153282006248488053) 2560000000000000000),
            (exactRationalLiteral (-8024792224052507) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-13097117049997135021) 2457600000000000000000),
            (exactRationalLiteral (-15920036708376389) 25600000000000000000),
            (exactRationalLiteral (1953792340688099) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-212107249886953992571) 9830400000000000000000),
            (exactRationalLiteral (767753570329034877) 102400000000000000000),
            (exactRationalLiteral (-48778998682127) 640000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-284418171354224388629) 9830400000000000000000),
            (exactRationalLiteral (2884290160335405939) 102400000000000000000),
            (exactRationalLiteral (-51125895653287493) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (42016736356535012471) 983040000000000000000),
            (exactRationalLiteral (-1416233320385411429) 51200000000000000000),
            (exactRationalLiteral (20319156037422499) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (13089015801586718363) 983040000000000000000),
            (exactRationalLiteral (-495817520875378097) 51200000000000000000),
            (exactRationalLiteral (381182582876843) 320000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14565153617252642789) 4915200000000000000000),
            (exactRationalLiteral (344377339792660211) 51200000000000000000),
            (exactRationalLiteral (406930743075407) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2079806770729014793) 9830400000000000000000),
            (exactRationalLiteral (-425540234652178369) 102400000000000000000),
            (exactRationalLiteral (-8500657832715193) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (67298426497490545777) 4915200000000000000000),
            (exactRationalLiteral (6000108322967213) 409600000000000000),
            (exactRationalLiteral (11519098591969729) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-113313378196955085587) 9830400000000000000000),
            (exactRationalLiteral (-1041947735172791771) 102400000000000000000),
            (exactRationalLiteral (-26130739202909027) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19879311419527385867) 983040000000000000000),
            (exactRationalLiteral (-478033478498863087) 51200000000000000000),
            (exactRationalLiteral (-604431078454139) 320000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5939093005659264369) 819200000000000000000),
            (exactRationalLiteral (189251654248327523) 25600000000000000000),
            (exactRationalLiteral (2584720368782259) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (8728885937659364573) 1638400000000000000000),
            (exactRationalLiteral (-5667907233259921) 51200000000000000000),
            (exactRationalLiteral (1748072693380359) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3725427216784501337) 1638400000000000000000),
            (exactRationalLiteral (338189366325667059) 51200000000000000000),
            (exactRationalLiteral (-7235517489210981) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-7125769702178255861) 614400000000000000000),
            (exactRationalLiteral (-39055516853299213) 1280000000000000000),
            (exactRationalLiteral (2723805016976371) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (268948621240135792907) 9830400000000000000000),
            (exactRationalLiteral (12762529113221382259) 102400000000000000000),
            (exactRationalLiteral (54753866987484827) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (283526703287689844461) 9830400000000000000000),
            (exactRationalLiteral (-19680651231576434011) 102400000000000000000),
            (exactRationalLiteral (-76350517802821447) 640000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-136694502476342960367) 1638400000000000000000),
            (exactRationalLiteral (989578759092941183) 10240000000000000000),
            (exactRationalLiteral (285209392374338691) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (16353353967592061249) 491520000000000000000),
            (exactRationalLiteral (81129835403693137) 5120000000000000000),
            (exactRationalLiteral (-17930024607968479) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (44201293390630436011) 9830400000000000000000),
            (exactRationalLiteral (-1921795364810018957) 102400000000000000000),
            (exactRationalLiteral (83556320209131259) 3200000000000000000),
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
          (exactRationalLiteral (689333118019029987) 20480000000000000000),
          (exactRationalLiteral (55214453694390111) 640000000000000000),
          (exactRationalLiteral (222240998353277563) 6400000000000000000),
          (exactRationalLiteral (38419636544030283383) 1228800000000000000000),
          (exactRationalLiteral (962788950762459431) 76800000000000000000),
          (exactRationalLiteral (506943949723929789) 204800000000000000000),
          (exactRationalLiteral (51187784528156153) 9600000000000000000),
          (exactRationalLiteral (459817370566372703) 61440000000000000000),
          (exactRationalLiteral (12604907755182354331) 614400000000000000000),
          (exactRationalLiteral (14564949238742055311) 1228800000000000000000),
          (exactRationalLiteral (8697909502423014317) 614400000000000000000),
          (exactRationalLiteral (84504961179722857) 245760000000000000000),
          (exactRationalLiteral (30452011668187151) 9600000000000000000),
          (exactRationalLiteral (130738417240780631) 9600000000000000000),
          (exactRationalLiteral (418738037644792799) 9600000000000000000),
          (exactRationalLiteral (190902261792577523) 6400000000000000000),
          (exactRationalLiteral (139590504331277661) 6400000000000000000),
          (exactRationalLiteral (328476960485177357) 61440000000000000000),
          (exactRationalLiteral (190757555586803863) 1600000000000000000),
          (exactRationalLiteral (2430765386427549413) 9600000000000000000),
          (exactRationalLiteral (190757555586803863) 1600000000000000000),
          (exactRationalLiteral (328476960485177357) 61440000000000000000),
          (exactRationalLiteral (139590504331277661) 6400000000000000000),
          (exactRationalLiteral (190902261792577523) 6400000000000000000),
          (exactRationalLiteral (418738037644792799) 9600000000000000000),
          (exactRationalLiteral (130738417240780631) 9600000000000000000),
          (exactRationalLiteral (30452011668187151) 9600000000000000000),
          (exactRationalLiteral (84504961179722857) 245760000000000000000),
          (exactRationalLiteral (8697909502423014317) 614400000000000000000),
          (exactRationalLiteral (14564949238742055311) 1228800000000000000000),
          (exactRationalLiteral (12604907755182354331) 614400000000000000000),
          (exactRationalLiteral (459817370566372703) 61440000000000000000),
          (exactRationalLiteral (51187784528156153) 9600000000000000000),
          (exactRationalLiteral (506943949723929789) 204800000000000000000),
          (exactRationalLiteral (962788950762459431) 76800000000000000000),
          (exactRationalLiteral (38419636544030283383) 1228800000000000000000),
          (exactRationalLiteral (222240998353277563) 6400000000000000000),
          (exactRationalLiteral (55214453694390111) 640000000000000000),
          (exactRationalLiteral (689333118019029987) 20480000000000000000),
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
      (31, 36),
      (31, 20),
      (31, 4),
      (30, 52),
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
      (27, 59)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (11214711325460356371) 3276800000000000000000),
            (exactRationalLiteral (-1602101617922908053) 102400000000000000000),
            (exactRationalLiteral (76290553234424193) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16633304144538474043) 491520000000000000000),
            (exactRationalLiteral (13575466881757081) 5120000000000000000),
            (exactRationalLiteral (-15847159652999549) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-125723360690273341221) 1638400000000000000000),
            (exactRationalLiteral (5990506303426339507) 51200000000000000000),
            (exactRationalLiteral (47219372321295621) 320000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (53783856929333952581) 3276800000000000000000),
            (exactRationalLiteral (-20962758608662910867) 102400000000000000000),
            (exactRationalLiteral (-259301099529131193) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (115277939898384295859) 3276800000000000000000),
            (exactRationalLiteral (12808033267090813163) 102400000000000000000),
            (exactRationalLiteral (-51202864084431) 5120000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2751931358985466613) 204800000000000000000),
            (exactRationalLiteral (-179904628890032601) 6400000000000000000),
            (exactRationalLiteral (4962672671255361) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (4366228136842838707) 1638400000000000000000),
            (exactRationalLiteral (299293682414593899) 51200000000000000000),
            (exactRationalLiteral (-12212324466325599) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (5235941567327122457) 983040000000000000000),
            (exactRationalLiteral (4364680908518407) 51200000000000000000),
            (exactRationalLiteral (653644275501761) 320000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (18983059041499430689) 2457600000000000000000),
            (exactRationalLiteral (199217263026599227) 25600000000000000000),
            (exactRationalLiteral (2398084020353593) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-34099109390175129311) 1638400000000000000000),
            (exactRationalLiteral (-97654853732392347) 10240000000000000000),
            (exactRationalLiteral (-2098239689278629) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-39964825265753593531) 3276800000000000000000),
            (exactRationalLiteral (-1154391851401445907) 102400000000000000000),
            (exactRationalLiteral (-30091318911418041) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (71938749762859229851) 4915200000000000000000),
            (exactRationalLiteral (797096354758599329) 51200000000000000000),
            (exactRationalLiteral (12022308601879123) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-4721208064676417731) 9830400000000000000000),
            (exactRationalLiteral (-90523772400782869) 20480000000000000000),
            (exactRationalLiteral (-1007731168630559) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12480487344893525143) 4915200000000000000000),
            (exactRationalLiteral (349509149163484331) 51200000000000000000),
            (exactRationalLiteral (21250038801401) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (12498896458767899849) 983040000000000000000),
            (exactRationalLiteral (-487475141125058521) 51200000000000000000),
            (exactRationalLiteral (2265276960775573) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (201825823235288872177) 4915200000000000000000),
            (exactRationalLiteral (-1337100944997117229) 51200000000000000000),
            (exactRationalLiteral (19247031656724601) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-89238101470127517229) 3276800000000000000000),
            (exactRationalLiteral (2685604942556681579) 102400000000000000000),
            (exactRationalLiteral (-48216713236074687) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-69168492081843815139) 3276800000000000000000),
            (exactRationalLiteral (765867470040025093) 102400000000000000000),
            (exactRationalLiteral (-699155151094257) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4389897617538097093) 819200000000000000000),
            (exactRationalLiteral (-8355412573201549) 25600000000000000000),
            (exactRationalLiteral (1828519726899321) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-9311658613711925783) 81920000000000000000),
            (exactRationalLiteral (734958121822225889) 12800000000000000000),
            (exactRationalLiteral (-7701162486054681) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1185399031382913247999) 4915200000000000000000),
            (exactRationalLiteral (-6379622023257154467) 51200000000000000000),
            (exactRationalLiteral (63060720672953143) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9311658613711925783) 81920000000000000000),
            (exactRationalLiteral (734958121822225889) 12800000000000000000),
            (exactRationalLiteral (-7701162486054681) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-4389897617538097093) 819200000000000000000),
            (exactRationalLiteral (-8355412573201549) 25600000000000000000),
            (exactRationalLiteral (1828519726899321) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-69168492081843815139) 3276800000000000000000),
            (exactRationalLiteral (765867470040025093) 102400000000000000000),
            (exactRationalLiteral (-699155151094257) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-89238101470127517229) 3276800000000000000000),
            (exactRationalLiteral (2685604942556681579) 102400000000000000000),
            (exactRationalLiteral (-48216713236074687) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (201825823235288872177) 4915200000000000000000),
            (exactRationalLiteral (-1337100944997117229) 51200000000000000000),
            (exactRationalLiteral (19247031656724601) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (12498896458767899849) 983040000000000000000),
            (exactRationalLiteral (-487475141125058521) 51200000000000000000),
            (exactRationalLiteral (2265276960775573) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-12480487344893525143) 4915200000000000000000),
            (exactRationalLiteral (349509149163484331) 51200000000000000000),
            (exactRationalLiteral (21250038801401) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-4721208064676417731) 9830400000000000000000),
            (exactRationalLiteral (-90523772400782869) 20480000000000000000),
            (exactRationalLiteral (-1007731168630559) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (71938749762859229851) 4915200000000000000000),
            (exactRationalLiteral (797096354758599329) 51200000000000000000),
            (exactRationalLiteral (12022308601879123) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-39964825265753593531) 3276800000000000000000),
            (exactRationalLiteral (-1154391851401445907) 102400000000000000000),
            (exactRationalLiteral (-30091318911418041) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-34099109390175129311) 1638400000000000000000),
            (exactRationalLiteral (-97654853732392347) 10240000000000000000),
            (exactRationalLiteral (-2098239689278629) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (18983059041499430689) 2457600000000000000000),
            (exactRationalLiteral (199217263026599227) 25600000000000000000),
            (exactRationalLiteral (2398084020353593) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (5235941567327122457) 983040000000000000000),
            (exactRationalLiteral (4364680908518407) 51200000000000000000),
            (exactRationalLiteral (653644275501761) 320000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4366228136842838707) 1638400000000000000000),
            (exactRationalLiteral (299293682414593899) 51200000000000000000),
            (exactRationalLiteral (-12212324466325599) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2751931358985466613) 204800000000000000000),
            (exactRationalLiteral (-179904628890032601) 6400000000000000000),
            (exactRationalLiteral (4962672671255361) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (115277939898384295859) 3276800000000000000000),
            (exactRationalLiteral (12808033267090813163) 102400000000000000000),
            (exactRationalLiteral (-51202864084431) 5120000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (53783856929333952581) 3276800000000000000000),
            (exactRationalLiteral (-20962758608662910867) 102400000000000000000),
            (exactRationalLiteral (-259301099529131193) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-125723360690273341221) 1638400000000000000000),
            (exactRationalLiteral (5990506303426339507) 51200000000000000000),
            (exactRationalLiteral (47219372321295621) 320000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (16633304144538474043) 491520000000000000000),
            (exactRationalLiteral (13575466881757081) 5120000000000000000),
            (exactRationalLiteral (-15847159652999549) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (11214711325460356371) 3276800000000000000000),
            (exactRationalLiteral (-1602101617922908053) 102400000000000000000),
            (exactRationalLiteral (76290553234424193) 3200000000000000000),
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
          (exactRationalLiteral (4835367921667552423) 1228800000000000000000),
          (exactRationalLiteral (173559222277039023) 5120000000000000000),
          (exactRationalLiteral (16433698088787319899) 204800000000000000000),
          (exactRationalLiteral (27925089696332588593) 1228800000000000000000),
          (exactRationalLiteral (1200370425930459037) 30720000000000000000),
          (exactRationalLiteral (34294923874162469) 2400000000000000000),
          (exactRationalLiteral (72695000421274811) 25600000000000000000),
          (exactRationalLiteral (136475867801227907) 25600000000000000000),
          (exactRationalLiteral (102019852939927473) 12800000000000000000),
          (exactRationalLiteral (1621374745901993953) 76800000000000000000),
          (exactRationalLiteral (1928904774969587921) 153600000000000000000),
          (exactRationalLiteral (1161974333717900311) 76800000000000000000),
          (exactRationalLiteral (95194525269106843) 153600000000000000000),
          (exactRationalLiteral (563611222420883419) 204800000000000000000),
          (exactRationalLiteral (7995440483259225731) 614400000000000000000),
          (exactRationalLiteral (25736925403430093327) 614400000000000000000),
          (exactRationalLiteral (34489652996121178361) 1228800000000000000000),
          (exactRationalLiteral (26225618561378245207) 1228800000000000000000),
          (exactRationalLiteral (206083377616563943) 38400000000000000000),
          (exactRationalLiteral (17737877359184090921) 153600000000000000000),
          (exactRationalLiteral (50197013516045531387) 204800000000000000000),
          (exactRationalLiteral (17737877359184090921) 153600000000000000000),
          (exactRationalLiteral (206083377616563943) 38400000000000000000),
          (exactRationalLiteral (26225618561378245207) 1228800000000000000000),
          (exactRationalLiteral (34489652996121178361) 1228800000000000000000),
          (exactRationalLiteral (25736925403430093327) 614400000000000000000),
          (exactRationalLiteral (7995440483259225731) 614400000000000000000),
          (exactRationalLiteral (563611222420883419) 204800000000000000000),
          (exactRationalLiteral (95194525269106843) 153600000000000000000),
          (exactRationalLiteral (1161974333717900311) 76800000000000000000),
          (exactRationalLiteral (1928904774969587921) 153600000000000000000),
          (exactRationalLiteral (1621374745901993953) 76800000000000000000),
          (exactRationalLiteral (102019852939927473) 12800000000000000000),
          (exactRationalLiteral (136475867801227907) 25600000000000000000),
          (exactRationalLiteral (72695000421274811) 25600000000000000000),
          (exactRationalLiteral (34294923874162469) 2400000000000000000),
          (exactRationalLiteral (1200370425930459037) 30720000000000000000),
          (exactRationalLiteral (27925089696332588593) 1228800000000000000000),
          (exactRationalLiteral (16433698088787319899) 204800000000000000000),
          (exactRationalLiteral (173559222277039023) 5120000000000000000),
          (exactRationalLiteral (4835367921667552423) 1228800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 37),
      (31, 21),
      (31, 5),
      (30, 53),
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
      (27, 58)
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
            (exactRationalLiteral (24917947839757882847) 9830400000000000000000),
            (exactRationalLiteral (-1311470938934625413) 102400000000000000000),
            (exactRationalLiteral (69024786259717127) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5510974163270965887) 163840000000000000000),
            (exactRationalLiteral (-9129488364060651) 1024000000000000000),
            (exactRationalLiteral (-13764294698030619) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-22572688802270379447) 327680000000000000000),
            (exactRationalLiteral (1367333737663306151) 10240000000000000000),
            (exactRationalLiteral (186984330838617519) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (32953211899614722393) 9830400000000000000000),
            (exactRationalLiteral (-4351012005561896711) 20480000000000000000),
            (exactRationalLiteral (-136849610044155151) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (421950975188903517247) 9830400000000000000000),
            (exactRationalLiteral (12506514792799227259) 102400000000000000000),
            (exactRationalLiteral (-118757447093023577) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9266714307624415153) 614400000000000000000),
            (exactRationalLiteral (-155576202896453177) 6400000000000000000),
            (exactRationalLiteral (7201540325534351) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (981866092234114257) 327680000000000000000),
            (exactRationalLiteral (240490770595062267) 51200000000000000000),
            (exactRationalLiteral (-17189131443440217) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (26251195173353342171) 4915200000000000000000),
            (exactRationalLiteral (20477863786810519) 51200000000000000000),
            (exactRationalLiteral (4788370061637251) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (20206393082509554503) 2457600000000000000000),
            (exactRationalLiteral (208436326411156267) 25600000000000000000),
            (exactRationalLiteral (2211447671924927) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-105248456995956533627) 4915200000000000000000),
            (exactRationalLiteral (-494819396013092119) 51200000000000000000),
            (exactRationalLiteral (-1174323986286563) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-127197765051440508583) 9830400000000000000000),
            (exactRationalLiteral (-1282678286464136099) 102400000000000000000),
            (exactRationalLiteral (-6810379723985411) 640000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (76867608434673012877) 4915200000000000000000),
            (exactRationalLiteral (846192009185934609) 51200000000000000000),
            (exactRationalLiteral (12525518611788517) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-7483537098859487749) 9830400000000000000000),
            (exactRationalLiteral (-465849481397400729) 102400000000000000000),
            (exactRationalLiteral (-1576653853590397) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3461023683084522299) 1638400000000000000000),
            (exactRationalLiteral (348627347552940411) 51200000000000000000),
            (exactRationalLiteral (-194430355061397) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (59598252226804020427) 4915200000000000000000),
            (exactRationalLiteral (-477695305189173513) 51200000000000000000),
            (exactRationalLiteral (2624641007166931) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (194029893447664072423) 4915200000000000000000),
            (exactRationalLiteral (-1262257067131614621) 51200000000000000000),
            (exactRationalLiteral (18174907276026703) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-252167638584206507233) 9830400000000000000000),
            (exactRationalLiteral (2498556454446808443) 102400000000000000000),
            (exactRationalLiteral (-45307530818861881) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-202920482327735160431) 9830400000000000000000),
            (exactRationalLiteral (762160329120280821) 102400000000000000000),
            (exactRationalLiteral (-1154415308777879) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13198384181785863833) 2457600000000000000000),
            (exactRationalLiteral (-1291878893181821) 25600000000000000000),
            (exactRationalLiteral (1703247113110543) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-135356249905626196279) 1228800000000000000000),
            (exactRationalLiteral (704800731354002817) 12800000000000000000),
            (exactRationalLiteral (-1475506549611371) 80000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (382622689909444099747) 1638400000000000000000),
            (exactRationalLiteral (-6132358222122071731) 51200000000000000000),
            (exactRationalLiteral (2422847195783529) 64000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-135356249905626196279) 1228800000000000000000),
            (exactRationalLiteral (704800731354002817) 12800000000000000000),
            (exactRationalLiteral (-1475506549611371) 80000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-13198384181785863833) 2457600000000000000000),
            (exactRationalLiteral (-1291878893181821) 25600000000000000000),
            (exactRationalLiteral (1703247113110543) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-202920482327735160431) 9830400000000000000000),
            (exactRationalLiteral (762160329120280821) 102400000000000000000),
            (exactRationalLiteral (-1154415308777879) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-252167638584206507233) 9830400000000000000000),
            (exactRationalLiteral (2498556454446808443) 102400000000000000000),
            (exactRationalLiteral (-45307530818861881) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (194029893447664072423) 4915200000000000000000),
            (exactRationalLiteral (-1262257067131614621) 51200000000000000000),
            (exactRationalLiteral (18174907276026703) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (59598252226804020427) 4915200000000000000000),
            (exactRationalLiteral (-477695305189173513) 51200000000000000000),
            (exactRationalLiteral (2624641007166931) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3461023683084522299) 1638400000000000000000),
            (exactRationalLiteral (348627347552940411) 51200000000000000000),
            (exactRationalLiteral (-194430355061397) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-7483537098859487749) 9830400000000000000000),
            (exactRationalLiteral (-465849481397400729) 102400000000000000000),
            (exactRationalLiteral (-1576653853590397) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (76867608434673012877) 4915200000000000000000),
            (exactRationalLiteral (846192009185934609) 51200000000000000000),
            (exactRationalLiteral (12525518611788517) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-127197765051440508583) 9830400000000000000000),
            (exactRationalLiteral (-1282678286464136099) 102400000000000000000),
            (exactRationalLiteral (-6810379723985411) 640000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-105248456995956533627) 4915200000000000000000),
            (exactRationalLiteral (-494819396013092119) 51200000000000000000),
            (exactRationalLiteral (-1174323986286563) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (20206393082509554503) 2457600000000000000000),
            (exactRationalLiteral (208436326411156267) 25600000000000000000),
            (exactRationalLiteral (2211447671924927) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (26251195173353342171) 4915200000000000000000),
            (exactRationalLiteral (20477863786810519) 51200000000000000000),
            (exactRationalLiteral (4788370061637251) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (981866092234114257) 327680000000000000000),
            (exactRationalLiteral (240490770595062267) 51200000000000000000),
            (exactRationalLiteral (-17189131443440217) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-9266714307624415153) 614400000000000000000),
            (exactRationalLiteral (-155576202896453177) 6400000000000000000),
            (exactRationalLiteral (7201540325534351) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (421950975188903517247) 9830400000000000000000),
            (exactRationalLiteral (12506514792799227259) 102400000000000000000),
            (exactRationalLiteral (-118757447093023577) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (32953211899614722393) 9830400000000000000000),
            (exactRationalLiteral (-4351012005561896711) 20480000000000000000),
            (exactRationalLiteral (-136849610044155151) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22572688802270379447) 327680000000000000000),
            (exactRationalLiteral (1367333737663306151) 10240000000000000000),
            (exactRationalLiteral (186984330838617519) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (5510974163270965887) 163840000000000000000),
            (exactRationalLiteral (-9129488364060651) 1024000000000000000),
            (exactRationalLiteral (-13764294698030619) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (24917947839757882847) 9830400000000000000000),
            (exactRationalLiteral (-1311470938934625413) 102400000000000000000),
            (exactRationalLiteral (69024786259717127) 3200000000000000000),
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
          (exactRationalLiteral (1527290897002628431) 153600000000000000000),
          (exactRationalLiteral (19127952891562583383) 409600000000000000000),
          (exactRationalLiteral (404613285896251339) 25600000000000000000),
          (exactRationalLiteral (641475329061584279) 204800000000000000000),
          (exactRationalLiteral (3290969243655093713) 614400000000000000000),
          (exactRationalLiteral (2604780385823072969) 307200000000000000000),
          (exactRationalLiteral (889466468317526447) 40960000000000000000),
          (exactRationalLiteral (5464580662356123023) 409600000000000000000),
          (exactRationalLiteral (9930501577883892119) 614400000000000000000),
          (exactRationalLiteral (1110510562952209991) 1228800000000000000000),
          (exactRationalLiteral (35722243268330119) 15360000000000000000),
          (exactRationalLiteral (190746976198030769) 15360000000000000000),
          (exactRationalLiteral (3091745709891833521) 76800000000000000000),
          (exactRationalLiteral (4059385705175189447) 153600000000000000000),
          (exactRationalLiteral (641281871659198421) 30720000000000000000),
          (exactRationalLiteral (825082291967828863) 153600000000000000000),
          (exactRationalLiteral (16783806947363449) 150000000000000000),
          (exactRationalLiteral (18225751604762054087) 76800000000000000000),
          (exactRationalLiteral (16783806947363449) 150000000000000000),
          (exactRationalLiteral (825082291967828863) 153600000000000000000),
          (exactRationalLiteral (641281871659198421) 30720000000000000000),
          (exactRationalLiteral (4059385705175189447) 153600000000000000000),
          (exactRationalLiteral (3091745709891833521) 76800000000000000000),
          (exactRationalLiteral (190746976198030769) 15360000000000000000),
          (exactRationalLiteral (35722243268330119) 15360000000000000000),
          (exactRationalLiteral (1110510562952209991) 1228800000000000000000),
          (exactRationalLiteral (9930501577883892119) 614400000000000000000),
          (exactRationalLiteral (5464580662356123023) 409600000000000000000),
          (exactRationalLiteral (889466468317526447) 40960000000000000000),
          (exactRationalLiteral (2604780385823072969) 307200000000000000000),
          (exactRationalLiteral (3290969243655093713) 614400000000000000000),
          (exactRationalLiteral (641475329061584279) 204800000000000000000),
          (exactRationalLiteral (404613285896251339) 25600000000000000000),
          (exactRationalLiteral (19127952891562583383) 409600000000000000000),
          (exactRationalLiteral (1527290897002628431) 153600000000000000000),
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
      (31, 38),
      (31, 22),
      (31, 6),
      (30, 54),
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
      (27, 57)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (17848356573367907629) 9830400000000000000000),
            (exactRationalLiteral (-1049903327845171037) 102400000000000000000),
            (exactRationalLiteral (61759019285010061) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16102197762334586423) 491520000000000000000),
            (exactRationalLiteral (-96538890702487871) 5120000000000000000),
            (exactRationalLiteral (-11681429743061689) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-98507652685721513097) 1638400000000000000000),
            (exactRationalLiteral (7486380950135279659) 51200000000000000000),
            (exactRationalLiteral (137871800070756933) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-98729537629832136581) 9830400000000000000000),
            (exactRationalLiteral (-882302219560646083) 4096000000000000000),
            (exactRationalLiteral (-14398120559179109) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (495217951952421581069) 9830400000000000000000),
            (exactRationalLiteral (11857973690346624547) 102400000000000000000),
            (exactRationalLiteral (-205513104133277779) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10104797570479606043) 614400000000000000000),
            (exactRationalLiteral (-122292306285757793) 6400000000000000000),
            (exactRationalLiteral (9440407979813341) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (5314919733950782127) 1638400000000000000000),
            (exactRationalLiteral (161780630867072163) 51200000000000000000),
            (exactRationalLiteral (-4433187684110967) 320000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8812534463850122027) 1638400000000000000000),
            (exactRationalLiteral (8534328280323283) 10240000000000000000),
            (exactRationalLiteral (6308518745765697) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1432186791176391771) 163840000000000000000),
            (exactRationalLiteral (216908844401998643) 25600000000000000000),
            (exactRationalLiteral (2024811323496261) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-108227769597058556833) 4915200000000000000000),
            (exactRationalLiteral (-497668860552254239) 51200000000000000000),
            (exactRationalLiteral (-250408283294497) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-135318299872498485893) 9830400000000000000000),
            (exactRationalLiteral (-1426807040360862347) 102400000000000000000),
            (exactRationalLiteral (-38012478328436069) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (82097079553169720311) 4915200000000000000000),
            (exactRationalLiteral (179460100730581493) 10240000000000000000),
            (exactRationalLiteral (13028728621697911) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2056741165105745459) 1966080000000000000000),
            (exactRationalLiteral (-465232092832637521) 102400000000000000000),
            (exactRationalLiteral (1885348135972001) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-8308986396220976291) 4915200000000000000000),
            (exactRationalLiteral (341731934961028451) 51200000000000000000),
            (exactRationalLiteral (-495110904129799) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (56765013543940547953) 4915200000000000000000),
            (exactRationalLiteral (-466478013067723073) 51200000000000000000),
            (exactRationalLiteral (2984005053558289) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (186670161434663913541) 4915200000000000000000),
            (exactRationalLiteral (-238340337357780721) 10240000000000000000),
            (exactRationalLiteral (3420556579065761) 320000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-237708353497683147923) 9830400000000000000000),
            (exactRationalLiteral (2323144696005786531) 102400000000000000000),
            (exactRationalLiteral (-1695933936065963) 128000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-198363194377349544541) 9830400000000000000000),
            (exactRationalLiteral (756632147569802061) 102400000000000000000),
            (exactRationalLiteral (-1609675466461501) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2637239516048556671) 491520000000000000000),
            (exactRationalLiteral (1054112866336559) 5120000000000000000),
            (exactRationalLiteral (315594899864353) 160000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-131214681391526870333) 1228800000000000000000),
            (exactRationalLiteral (675937859837771049) 12800000000000000000),
            (exactRationalLiteral (-7053903010059029) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1111790816391221467883) 4915200000000000000000),
            (exactRationalLiteral (-5895052584100448667) 51200000000000000000),
            (exactRationalLiteral (58081639116223307) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-131214681391526870333) 1228800000000000000000),
            (exactRationalLiteral (675937859837771049) 12800000000000000000),
            (exactRationalLiteral (-7053903010059029) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-2637239516048556671) 491520000000000000000),
            (exactRationalLiteral (1054112866336559) 5120000000000000000),
            (exactRationalLiteral (315594899864353) 160000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-198363194377349544541) 9830400000000000000000),
            (exactRationalLiteral (756632147569802061) 102400000000000000000),
            (exactRationalLiteral (-1609675466461501) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-237708353497683147923) 9830400000000000000000),
            (exactRationalLiteral (2323144696005786531) 102400000000000000000),
            (exactRationalLiteral (-1695933936065963) 128000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (186670161434663913541) 4915200000000000000000),
            (exactRationalLiteral (-238340337357780721) 10240000000000000000),
            (exactRationalLiteral (3420556579065761) 320000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (56765013543940547953) 4915200000000000000000),
            (exactRationalLiteral (-466478013067723073) 51200000000000000000),
            (exactRationalLiteral (2984005053558289) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-8308986396220976291) 4915200000000000000000),
            (exactRationalLiteral (341731934961028451) 51200000000000000000),
            (exactRationalLiteral (-495110904129799) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2056741165105745459) 1966080000000000000000),
            (exactRationalLiteral (-465232092832637521) 102400000000000000000),
            (exactRationalLiteral (1885348135972001) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (82097079553169720311) 4915200000000000000000),
            (exactRationalLiteral (179460100730581493) 10240000000000000000),
            (exactRationalLiteral (13028728621697911) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-135318299872498485893) 9830400000000000000000),
            (exactRationalLiteral (-1426807040360862347) 102400000000000000000),
            (exactRationalLiteral (-38012478328436069) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-108227769597058556833) 4915200000000000000000),
            (exactRationalLiteral (-497668860552254239) 51200000000000000000),
            (exactRationalLiteral (-250408283294497) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1432186791176391771) 163840000000000000000),
            (exactRationalLiteral (216908844401998643) 25600000000000000000),
            (exactRationalLiteral (2024811323496261) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (8812534463850122027) 1638400000000000000000),
            (exactRationalLiteral (8534328280323283) 10240000000000000000),
            (exactRationalLiteral (6308518745765697) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5314919733950782127) 1638400000000000000000),
            (exactRationalLiteral (161780630867072163) 51200000000000000000),
            (exactRationalLiteral (-4433187684110967) 320000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-10104797570479606043) 614400000000000000000),
            (exactRationalLiteral (-122292306285757793) 6400000000000000000),
            (exactRationalLiteral (9440407979813341) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (495217951952421581069) 9830400000000000000000),
            (exactRationalLiteral (11857973690346624547) 102400000000000000000),
            (exactRationalLiteral (-205513104133277779) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-98729537629832136581) 9830400000000000000000),
            (exactRationalLiteral (-882302219560646083) 4096000000000000000),
            (exactRationalLiteral (-14398120559179109) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-98507652685721513097) 1638400000000000000000),
            (exactRationalLiteral (7486380950135279659) 51200000000000000000),
            (exactRationalLiteral (137871800070756933) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (16102197762334586423) 491520000000000000000),
            (exactRationalLiteral (-96538890702487871) 5120000000000000000),
            (exactRationalLiteral (-11681429743061689) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (17848356573367907629) 9830400000000000000000),
            (exactRationalLiteral (-1049903327845171037) 102400000000000000000),
            (exactRationalLiteral (61759019285010061) 3200000000000000000),
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
          (exactRationalLiteral (882790687426908519) 409600000000000000000),
          (exactRationalLiteral (2044466089091922563) 61440000000000000000),
          (exactRationalLiteral (13230997051748924049) 204800000000000000000),
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
          (exactRationalLiteral (1167607145411667203) 614400000000000000000),
          (exactRationalLiteral (1454330497907029909) 122880000000000000000),
          (exactRationalLiteral (4757427772647673993) 122880000000000000000),
          (exactRationalLiteral (10200268217588085881) 409600000000000000000),
          (exactRationalLiteral (8359903842349145559) 409600000000000000000),
          (exactRationalLiteral (549883863059707169) 102400000000000000000),
          (exactRationalLiteral (1110531820791161329) 10240000000000000000),
          (exactRationalLiteral (141206432978907583283) 614400000000000000000),
          (exactRationalLiteral (1110531820791161329) 10240000000000000000),
          (exactRationalLiteral (549883863059707169) 102400000000000000000),
          (exactRationalLiteral (8359903842349145559) 409600000000000000000),
          (exactRationalLiteral (10200268217588085881) 409600000000000000000),
          (exactRationalLiteral (4757427772647673993) 122880000000000000000),
          (exactRationalLiteral (1454330497907029909) 122880000000000000000),
          (exactRationalLiteral (1167607145411667203) 614400000000000000000),
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
          (exactRationalLiteral (13230997051748924049) 204800000000000000000),
          (exactRationalLiteral (2044466089091922563) 61440000000000000000),
          (exactRationalLiteral (882790687426908519) 409600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 39),
      (31, 23),
      (31, 7),
      (30, 55),
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
      (27, 56)
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
            (exactRationalLiteral (32695951386181797) 26214400000000000000),
            (exactRationalLiteral (-32695951386181797) 4096000000000000000),
            (exactRationalLiteral (10898650462060599) 640000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (15391118721022794649) 491520000000000000000),
            (exactRationalLiteral (-139098879764796767) 5120000000000000000),
            (exactRationalLiteral (-9598564788092759) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-16609777391905014699) 327680000000000000000),
            (exactRationalLiteral (7939643088882586219) 51200000000000000000),
            (exactRationalLiteral (88759269302896347) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-76919280684233098057) 3276800000000000000000),
            (exactRationalLiteral (-21870244992282916427) 102400000000000000000),
            (exactRationalLiteral (108053368925796933) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (37570174281116065213) 655360000000000000000),
            (exactRationalLiteral (10862409959733005027) 102400000000000000000),
            (exactRationalLiteral (-292268761173531981) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3572103680606425583) 204800000000000000000),
            (exactRationalLiteral (-80052939057946449) 6400000000000000000),
            (exactRationalLiteral (11679275634092331) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (5543181499366554289) 1638400000000000000000),
            (exactRationalLiteral (63163263230623587) 51200000000000000000),
            (exactRationalLiteral (-27142745397669453) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (26775416059645766719) 4915200000000000000000),
            (exactRationalLiteral (14189202750587219) 10240000000000000000),
            (exactRationalLiteral (7828667429894143) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (22807806124546108891) 2457600000000000000000),
            (exactRationalLiteral (44926963399825271) 5120000000000000000),
            (exactRationalLiteral (367634995013519) 160000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-37071030665653215989) 1638400000000000000000),
            (exactRationalLiteral (-99364532455889619) 10240000000000000000),
            (exactRationalLiteral (673507419697569) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-48117044724479642953) 3276800000000000000000),
            (exactRationalLiteral (-1586778113091624651) 102400000000000000000),
            (exactRationalLiteral (-41973058036945083) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (87639240158587177609) 4915200000000000000000),
            (exactRationalLiteral (950421838159517897) 51200000000000000000),
            (exactRationalLiteral (2706387726321461) 320000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-13038626196934638817) 9830400000000000000000),
            (exactRationalLiteral (-450766696309624721) 102400000000000000000),
            (exactRationalLiteral (5347350125534399) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1258863010336792313) 983040000000000000000),
            (exactRationalLiteral (328822911387748451) 51200000000000000000),
            (exactRationalLiteral (-795791453198201) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (10800678196472494883) 983040000000000000000),
            (exactRationalLiteral (-453823264760707201) 51200000000000000000),
            (exactRationalLiteral (3343369099949647) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (179720896211151645979) 4915200000000000000000),
            (exactRationalLiteral (-1125434803968984181) 51200000000000000000),
            (exactRationalLiteral (16030658514630907) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-74755542924266455471) 3276800000000000000000),
            (exactRationalLiteral (2159369667233615843) 102400000000000000000),
            (exactRationalLiteral (-39489165984436269) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2584593848508786729) 131072000000000000000),
            (exactRationalLiteral (749282925388588813) 102400000000000000000),
            (exactRationalLiteral (-2064935624145123) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4378713196905326839) 819200000000000000000),
            (exactRationalLiteral (11331917101392299) 25600000000000000000),
            (exactRationalLiteral (1452701885532987) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-42414135516556320361) 409600000000000000000),
            (exactRationalLiteral (129673901454706117) 2560000000000000000),
            (exactRationalLiteral (-6730273272061203) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1077107522392899995893) 4915200000000000000000),
            (exactRationalLiteral (-226708204367691411) 2048000000000000000),
            (exactRationalLiteral (55592098337858389) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-42414135516556320361) 409600000000000000000),
            (exactRationalLiteral (129673901454706117) 2560000000000000000),
            (exactRationalLiteral (-6730273272061203) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-4378713196905326839) 819200000000000000000),
            (exactRationalLiteral (11331917101392299) 25600000000000000000),
            (exactRationalLiteral (1452701885532987) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2584593848508786729) 131072000000000000000),
            (exactRationalLiteral (749282925388588813) 102400000000000000000),
            (exactRationalLiteral (-2064935624145123) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-74755542924266455471) 3276800000000000000000),
            (exactRationalLiteral (2159369667233615843) 102400000000000000000),
            (exactRationalLiteral (-39489165984436269) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (179720896211151645979) 4915200000000000000000),
            (exactRationalLiteral (-1125434803968984181) 51200000000000000000),
            (exactRationalLiteral (16030658514630907) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10800678196472494883) 983040000000000000000),
            (exactRationalLiteral (-453823264760707201) 51200000000000000000),
            (exactRationalLiteral (3343369099949647) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1258863010336792313) 983040000000000000000),
            (exactRationalLiteral (328822911387748451) 51200000000000000000),
            (exactRationalLiteral (-795791453198201) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-13038626196934638817) 9830400000000000000000),
            (exactRationalLiteral (-450766696309624721) 102400000000000000000),
            (exactRationalLiteral (5347350125534399) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (87639240158587177609) 4915200000000000000000),
            (exactRationalLiteral (950421838159517897) 51200000000000000000),
            (exactRationalLiteral (2706387726321461) 320000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-48117044724479642953) 3276800000000000000000),
            (exactRationalLiteral (-1586778113091624651) 102400000000000000000),
            (exactRationalLiteral (-41973058036945083) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-37071030665653215989) 1638400000000000000000),
            (exactRationalLiteral (-99364532455889619) 10240000000000000000),
            (exactRationalLiteral (673507419697569) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (22807806124546108891) 2457600000000000000000),
            (exactRationalLiteral (44926963399825271) 5120000000000000000),
            (exactRationalLiteral (367634995013519) 160000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (26775416059645766719) 4915200000000000000000),
            (exactRationalLiteral (14189202750587219) 10240000000000000000),
            (exactRationalLiteral (7828667429894143) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5543181499366554289) 1638400000000000000000),
            (exactRationalLiteral (63163263230623587) 51200000000000000000),
            (exactRationalLiteral (-27142745397669453) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3572103680606425583) 204800000000000000000),
            (exactRationalLiteral (-80052939057946449) 6400000000000000000),
            (exactRationalLiteral (11679275634092331) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (37570174281116065213) 655360000000000000000),
            (exactRationalLiteral (10862409959733005027) 102400000000000000000),
            (exactRationalLiteral (-292268761173531981) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-76919280684233098057) 3276800000000000000000),
            (exactRationalLiteral (-21870244992282916427) 102400000000000000000),
            (exactRationalLiteral (108053368925796933) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16609777391905014699) 327680000000000000000),
            (exactRationalLiteral (7939643088882586219) 51200000000000000000),
            (exactRationalLiteral (88759269302896347) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15391118721022794649) 491520000000000000000),
            (exactRationalLiteral (-139098879764796767) 5120000000000000000),
            (exactRationalLiteral (-9598564788092759) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 26214400000000000000),
            (exactRationalLiteral (-32695951386181797) 4096000000000000000),
            (exactRationalLiteral (10898650462060599) 640000000000000000),
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
          (exactRationalLiteral (36997898897253520579) 1228800000000000000000),
          (exactRationalLiteral (74402457497987408779) 1228800000000000000000),
          (exactRationalLiteral (1365039074782962451) 76800000000000000000),
          (exactRationalLiteral (139459313734249733) 40960000000000000000),
          (exactRationalLiteral (1125520840730680069) 204800000000000000000),
          (exactRationalLiteral (978630490928936517) 102400000000000000000),
          (exactRationalLiteral (14087634687960925439) 614400000000000000000),
          (exactRationalLiteral (18654920997084861571) 1228800000000000000000),
          (exactRationalLiteral (11316419136745688489) 614400000000000000000),
          (exactRationalLiteral (1796644154311516073) 1228800000000000000000),
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
          (exactRationalLiteral (1796644154311516073) 1228800000000000000000),
          (exactRationalLiteral (11316419136745688489) 614400000000000000000),
          (exactRationalLiteral (18654920997084861571) 1228800000000000000000),
          (exactRationalLiteral (14087634687960925439) 614400000000000000000),
          (exactRationalLiteral (978630490928936517) 102400000000000000000),
          (exactRationalLiteral (1125520840730680069) 204800000000000000000),
          (exactRationalLiteral (139459313734249733) 40960000000000000000),
          (exactRationalLiteral (1365039074782962451) 76800000000000000000),
          (exactRationalLiteral (74402457497987408779) 1228800000000000000000),
          (exactRationalLiteral (36997898897253520579) 1228800000000000000000),
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
      (31, 40),
      (31, 24),
      (31, 8),
      (30, 56),
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
      (27, 55)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (7981445021715712001) 9830400000000000000000),
            (exactRationalLiteral (-613957309362747077) 102400000000000000000),
            (exactRationalLiteral (47227485335595929) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4816558041598925553) 163840000000000000000),
            (exactRationalLiteral (-173327409007229943) 5120000000000000000),
            (exactRationalLiteral (-7515699833123829) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-66880047078905463117) 1638400000000000000000),
            (exactRationalLiteral (1639291020911690087) 10240000000000000000),
            (exactRationalLiteral (39646738535035761) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-360192865621347325369) 9830400000000000000000),
            (exactRationalLiteral (-21193128537609776611) 102400000000000000000),
            (exactRationalLiteral (9220194336430919) 128000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (624872826212895607777) 9830400000000000000000),
            (exactRationalLiteral (9519823600958368699) 102400000000000000000),
            (exactRationalLiteral (-379024418213786183) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11047521897940731511) 614400000000000000000),
            (exactRationalLiteral (-5771620242603829) 1280000000000000000),
            (exactRationalLiteral (13918143288371321) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (5554301301600970827) 1638400000000000000000),
            (exactRationalLiteral (-55361332314283461) 51200000000000000000),
            (exactRationalLiteral (-32119552374784071) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (27301116746058626789) 4915200000000000000000),
            (exactRationalLiteral (105300980840769559) 51200000000000000000),
            (exactRationalLiteral (9348816114022589) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (24176926580847963497) 2457600000000000000000),
            (exactRationalLiteral (231614244202539403) 25600000000000000000),
            (exactRationalLiteral (1651538626638929) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-22836450043757599489) 983040000000000000000),
            (exactRationalLiteral (-492280801194673687) 51200000000000000000),
            (exactRationalLiteral (319484624537927) 320000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-154391321867266053817) 9830400000000000000000),
            (exactRationalLiteral (-1762591504656423011) 102400000000000000000),
            (exactRationalLiteral (-45933637745454097) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (93506167291163210227) 4915200000000000000000),
            (exactRationalLiteral (201111202541153181) 10240000000000000000),
            (exactRationalLiteral (14035148641516699) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-15665210165327724763) 9830400000000000000000),
            (exactRationalLiteral (-422453291828362329) 102400000000000000000),
            (exactRationalLiteral (8809352115096797) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1458379560510243653) 1638400000000000000000),
            (exactRationalLiteral (309900276833100411) 51200000000000000000),
            (exactRationalLiteral (-1096472002266603) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (10264401855836638481) 983040000000000000000),
            (exactRationalLiteral (-439731060268125897) 51200000000000000000),
            (exactRationalLiteral (740546629268201) 320000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (34631273358398104037) 983040000000000000000),
            (exactRationalLiteral (-1063456418671856349) 51200000000000000000),
            (exactRationalLiteral (14958534133933009) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-211772644031542055359) 9830400000000000000000),
            (exactRationalLiteral (2007231368130296379) 102400000000000000000),
            (exactRationalLiteral (-36579983567223463) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-189375441353947947761) 9830400000000000000000),
            (exactRationalLiteral (740112662576641077) 102400000000000000000),
            (exactRationalLiteral (-504039156365749) 640000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13051216755936385991) 2457600000000000000000),
            (exactRationalLiteral (16892179415946691) 25600000000000000000),
            (exactRationalLiteral (1327429271744209) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-24686331653268104141) 245760000000000000000),
            (exactRationalLiteral (24883826946451257) 512000000000000000),
            (exactRationalLiteral (-6406643534063377) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (347919479584895708413) 1638400000000000000000),
            (exactRationalLiteral (-1090063159479516311) 10240000000000000000),
            (exactRationalLiteral (53102557559493471) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-24686331653268104141) 245760000000000000000),
            (exactRationalLiteral (24883826946451257) 512000000000000000),
            (exactRationalLiteral (-6406643534063377) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-13051216755936385991) 2457600000000000000000),
            (exactRationalLiteral (16892179415946691) 25600000000000000000),
            (exactRationalLiteral (1327429271744209) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-189375441353947947761) 9830400000000000000000),
            (exactRationalLiteral (740112662576641077) 102400000000000000000),
            (exactRationalLiteral (-504039156365749) 640000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-211772644031542055359) 9830400000000000000000),
            (exactRationalLiteral (2007231368130296379) 102400000000000000000),
            (exactRationalLiteral (-36579983567223463) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (34631273358398104037) 983040000000000000000),
            (exactRationalLiteral (-1063456418671856349) 51200000000000000000),
            (exactRationalLiteral (14958534133933009) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10264401855836638481) 983040000000000000000),
            (exactRationalLiteral (-439731060268125897) 51200000000000000000),
            (exactRationalLiteral (740546629268201) 320000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1458379560510243653) 1638400000000000000000),
            (exactRationalLiteral (309900276833100411) 51200000000000000000),
            (exactRationalLiteral (-1096472002266603) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-15665210165327724763) 9830400000000000000000),
            (exactRationalLiteral (-422453291828362329) 102400000000000000000),
            (exactRationalLiteral (8809352115096797) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (93506167291163210227) 4915200000000000000000),
            (exactRationalLiteral (201111202541153181) 10240000000000000000),
            (exactRationalLiteral (14035148641516699) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-154391321867266053817) 9830400000000000000000),
            (exactRationalLiteral (-1762591504656423011) 102400000000000000000),
            (exactRationalLiteral (-45933637745454097) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22836450043757599489) 983040000000000000000),
            (exactRationalLiteral (-492280801194673687) 51200000000000000000),
            (exactRationalLiteral (319484624537927) 320000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (24176926580847963497) 2457600000000000000000),
            (exactRationalLiteral (231614244202539403) 25600000000000000000),
            (exactRationalLiteral (1651538626638929) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (27301116746058626789) 4915200000000000000000),
            (exactRationalLiteral (105300980840769559) 51200000000000000000),
            (exactRationalLiteral (9348816114022589) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5554301301600970827) 1638400000000000000000),
            (exactRationalLiteral (-55361332314283461) 51200000000000000000),
            (exactRationalLiteral (-32119552374784071) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-11047521897940731511) 614400000000000000000),
            (exactRationalLiteral (-5771620242603829) 1280000000000000000),
            (exactRationalLiteral (13918143288371321) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (624872826212895607777) 9830400000000000000000),
            (exactRationalLiteral (9519823600958368699) 102400000000000000000),
            (exactRationalLiteral (-379024418213786183) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-360192865621347325369) 9830400000000000000000),
            (exactRationalLiteral (-21193128537609776611) 102400000000000000000),
            (exactRationalLiteral (9220194336430919) 128000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-66880047078905463117) 1638400000000000000000),
            (exactRationalLiteral (1639291020911690087) 10240000000000000000),
            (exactRationalLiteral (39646738535035761) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (4816558041598925553) 163840000000000000000),
            (exactRationalLiteral (-173327409007229943) 5120000000000000000),
            (exactRationalLiteral (-7515699833123829) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (7981445021715712001) 9830400000000000000000),
            (exactRationalLiteral (-613957309362747077) 102400000000000000000),
            (exactRationalLiteral (47227485335595929) 3200000000000000000),
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
          (exactRationalLiteral (1246079036162261819) 1228800000000000000000),
          (exactRationalLiteral (1868258477480201317) 61440000000000000000),
          (exactRationalLiteral (1875716750578355859) 40960000000000000000),
          (exactRationalLiteral (2203226619344801293) 51200000000000000000),
          (exactRationalLiteral (3397145030899006397) 51200000000000000000),
          (exactRationalLiteral (115535599752804807) 6400000000000000000),
          (exactRationalLiteral (348914508041737973) 102400000000000000000),
          (exactRationalLiteral (431966034551016679) 76800000000000000000),
          (exactRationalLiteral (77739470659879013) 7680000000000000000),
          (exactRationalLiteral (602363741641419029) 25600000000000000000),
          (exactRationalLiteral (832389987418364269) 51200000000000000000),
          (exactRationalLiteral (1508831130940781449) 76800000000000000000),
          (exactRationalLiteral (52826284323352313) 30720000000000000000),
          (exactRationalLiteral (665066861336420029) 614400000000000000000),
          (exactRationalLiteral (6581516372175424679) 614400000000000000000),
          (exactRationalLiteral (22049018464074779651) 614400000000000000000),
          (exactRationalLiteral (27238191584730402661) 1228800000000000000000),
          (exactRationalLiteral (23950389037368064427) 1228800000000000000000),
          (exactRationalLiteral (1637231046257762381) 307200000000000000000),
          (exactRationalLiteral (15664665879099444253) 153600000000000000000),
          (exactRationalLiteral (132533742323743441597) 614400000000000000000),
          (exactRationalLiteral (15664665879099444253) 153600000000000000000),
          (exactRationalLiteral (1637231046257762381) 307200000000000000000),
          (exactRationalLiteral (23950389037368064427) 1228800000000000000000),
          (exactRationalLiteral (27238191584730402661) 1228800000000000000000),
          (exactRationalLiteral (22049018464074779651) 614400000000000000000),
          (exactRationalLiteral (6581516372175424679) 614400000000000000000),
          (exactRationalLiteral (665066861336420029) 614400000000000000000),
          (exactRationalLiteral (52826284323352313) 30720000000000000000),
          (exactRationalLiteral (1508831130940781449) 76800000000000000000),
          (exactRationalLiteral (832389987418364269) 51200000000000000000),
          (exactRationalLiteral (602363741641419029) 25600000000000000000),
          (exactRationalLiteral (77739470659879013) 7680000000000000000),
          (exactRationalLiteral (431966034551016679) 76800000000000000000),
          (exactRationalLiteral (348914508041737973) 102400000000000000000),
          (exactRationalLiteral (115535599752804807) 6400000000000000000),
          (exactRationalLiteral (3397145030899006397) 51200000000000000000),
          (exactRationalLiteral (2203226619344801293) 51200000000000000000),
          (exactRationalLiteral (1875716750578355859) 40960000000000000000),
          (exactRationalLiteral (1868258477480201317) 61440000000000000000),
          (exactRationalLiteral (1246079036162261819) 1228800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 41),
      (31, 25),
      (31, 9),
      (30, 57),
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
      (27, 54)
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
theorem generatorCoordinates31_valid : ∀ i, (generatorCoordinates31 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
