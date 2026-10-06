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

/-- Actual coordinate interval candidates, block 19. -/
def generatorCoordinates19 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 4
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
            (exactRationalLiteral (1503511111387821029) 307200000000000000000),
            (exactRationalLiteral (-115654700875986233) 6400000000000000000),
            (exactRationalLiteral (8896515451998941) 400000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2126345101184823603) 81920000000000000000),
            (exactRationalLiteral (140745870175409571) 5120000000000000000),
            (exactRationalLiteral (-32600429312789583) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-43849059671735851543) 614400000000000000000),
            (exactRationalLiteral (693074901345948587) 12800000000000000000),
            (exactRationalLiteral (142316280370786577) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (205496841085155581) 6400000000000000000),
            (exactRationalLiteral (-225573530150475297) 1600000000000000000),
            (exactRationalLiteral (-284501575882857) 2000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (10171679163184007431) 614400000000000000000),
            (exactRationalLiteral (258835644829995361) 2560000000000000000),
            (exactRationalLiteral (36496440098751967) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5202112617558241241) 614400000000000000000),
            (exactRationalLiteral (-346763236520396403) 12800000000000000000),
            (exactRationalLiteral (-18762614403833) 32000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5977503039304877) 10240000000000000000),
            (exactRationalLiteral (16325593202770669) 3200000000000000000),
            (exactRationalLiteral (-34361636710089) 40000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1079953730199252469) 1228800000000000000000),
            (exactRationalLiteral (-7847468296472811) 5120000000000000000),
            (exactRationalLiteral (-150084102239533) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-538606922587838111) 1228800000000000000000),
            (exactRationalLiteral (5823500122773099) 25600000000000000000),
            (exactRationalLiteral (-67512653220263) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (27070322627416583) 409600000000000000000),
            (exactRationalLiteral (1597224281247479) 25600000000000000000),
            (exactRationalLiteral (20509768141737) 320000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1013719196013433001) 614400000000000000000),
            (exactRationalLiteral (10360224307268843) 12800000000000000000),
            (exactRationalLiteral (-8257584065839) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (33684471893408303) 204800000000000000000),
            (exactRationalLiteral (8737121219549479) 12800000000000000000),
            (exactRationalLiteral (472250076975669) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2765713859218478693) 307200000000000000000),
            (exactRationalLiteral (-41164076106011) 51200000000000000),
            (exactRationalLiteral (-336703373180621) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-2053486553133411091) 409600000000000000000),
            (exactRationalLiteral (10525993782418829) 25600000000000000000),
            (exactRationalLiteral (1214559565082127) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5560323102669905731) 1228800000000000000000),
            (exactRationalLiteral (20888220402648947) 5120000000000000000),
            (exactRationalLiteral (1252688903774741) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22645781725394395703) 1228800000000000000000),
            (exactRationalLiteral (173973769434849747) 25600000000000000000),
            (exactRationalLiteral (6877006528699681) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-76507586523635968297) 1228800000000000000000),
            (exactRationalLiteral (497083940263814013) 25600000000000000000),
            (exactRationalLiteral (34487658692217119) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-218038475426738526259) 614400000000000000000),
            (exactRationalLiteral (3870363883652266367) 12800000000000000000),
            (exactRationalLiteral (298006959131071493) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (76110652423555344341) 38400000000000000000),
            (exactRationalLiteral (-207625620217903193) 400000000000000000),
            (exactRationalLiteral (-132219533415688441) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-862118914771207035703) 409600000000000000000),
            (exactRationalLiteral (-31929109786447062759) 25600000000000000000),
            (exactRationalLiteral (9376736936633139747) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (54546398545518197309) 204800000000000000000),
            (exactRationalLiteral (38571213101117958141) 12800000000000000000),
            (exactRationalLiteral (-4699663457249959617) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (140044991074306740919) 307200000000000000000),
            (exactRationalLiteral (-13509361992675625647) 6400000000000000000),
            (exactRationalLiteral (229196328433219211) 80000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1287297767918297489617) 1228800000000000000000),
            (exactRationalLiteral (35218537372651796469) 25600000000000000000),
            (exactRationalLiteral (-360762933999461333) 320000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (553827056153305250671) 307200000000000000000),
            (exactRationalLiteral (-10831216660526106139) 6400000000000000000),
            (exactRationalLiteral (416947846841612599) 400000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1287297767918297489617) 1228800000000000000000),
            (exactRationalLiteral (35218537372651796469) 25600000000000000000),
            (exactRationalLiteral (-360762933999461333) 320000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (140044991074306740919) 307200000000000000000),
            (exactRationalLiteral (-13509361992675625647) 6400000000000000000),
            (exactRationalLiteral (229196328433219211) 80000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (54546398545518197309) 204800000000000000000),
            (exactRationalLiteral (38571213101117958141) 12800000000000000000),
            (exactRationalLiteral (-4699663457249959617) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-862118914771207035703) 409600000000000000000),
            (exactRationalLiteral (-31929109786447062759) 25600000000000000000),
            (exactRationalLiteral (9376736936633139747) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (76110652423555344341) 38400000000000000000),
            (exactRationalLiteral (-207625620217903193) 400000000000000000),
            (exactRationalLiteral (-132219533415688441) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-218038475426738526259) 614400000000000000000),
            (exactRationalLiteral (3870363883652266367) 12800000000000000000),
            (exactRationalLiteral (298006959131071493) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-76507586523635968297) 1228800000000000000000),
            (exactRationalLiteral (497083940263814013) 25600000000000000000),
            (exactRationalLiteral (34487658692217119) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22645781725394395703) 1228800000000000000000),
            (exactRationalLiteral (173973769434849747) 25600000000000000000),
            (exactRationalLiteral (6877006528699681) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5560323102669905731) 1228800000000000000000),
            (exactRationalLiteral (20888220402648947) 5120000000000000000),
            (exactRationalLiteral (1252688903774741) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2053486553133411091) 409600000000000000000),
            (exactRationalLiteral (10525993782418829) 25600000000000000000),
            (exactRationalLiteral (1214559565082127) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2765713859218478693) 307200000000000000000),
            (exactRationalLiteral (-41164076106011) 51200000000000000),
            (exactRationalLiteral (-336703373180621) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (33684471893408303) 204800000000000000000),
            (exactRationalLiteral (8737121219549479) 12800000000000000000),
            (exactRationalLiteral (472250076975669) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1013719196013433001) 614400000000000000000),
            (exactRationalLiteral (10360224307268843) 12800000000000000000),
            (exactRationalLiteral (-8257584065839) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27070322627416583) 409600000000000000000),
            (exactRationalLiteral (1597224281247479) 25600000000000000000),
            (exactRationalLiteral (20509768141737) 320000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-538606922587838111) 1228800000000000000000),
            (exactRationalLiteral (5823500122773099) 25600000000000000000),
            (exactRationalLiteral (-67512653220263) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1079953730199252469) 1228800000000000000000),
            (exactRationalLiteral (-7847468296472811) 5120000000000000000),
            (exactRationalLiteral (-150084102239533) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (5977503039304877) 10240000000000000000),
            (exactRationalLiteral (16325593202770669) 3200000000000000000),
            (exactRationalLiteral (-34361636710089) 40000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-5202112617558241241) 614400000000000000000),
            (exactRationalLiteral (-346763236520396403) 12800000000000000000),
            (exactRationalLiteral (-18762614403833) 32000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (10171679163184007431) 614400000000000000000),
            (exactRationalLiteral (258835644829995361) 2560000000000000000),
            (exactRationalLiteral (36496440098751967) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (205496841085155581) 6400000000000000000),
            (exactRationalLiteral (-225573530150475297) 1600000000000000000),
            (exactRationalLiteral (-284501575882857) 2000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-43849059671735851543) 614400000000000000000),
            (exactRationalLiteral (693074901345948587) 12800000000000000000),
            (exactRationalLiteral (142316280370786577) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2126345101184823603) 81920000000000000000),
            (exactRationalLiteral (140745870175409571) 5120000000000000000),
            (exactRationalLiteral (-32600429312789583) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (1503511111387821029) 307200000000000000000),
            (exactRationalLiteral (-115654700875986233) 6400000000000000000),
            (exactRationalLiteral (8896515451998941) 400000000000000000),
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
          (exactRationalLiteral (234731138464279751) 38400000000000000000),
          (exactRationalLiteral (34930886317647829) 1280000000000000000),
          (exactRationalLiteral (5685168566763805313) 76800000000000000000),
          (exactRationalLiteral (774191556766925239) 19200000000000000000),
          (exactRationalLiteral (73670223963497773) 3200000000000000000),
          (exactRationalLiteral (97435126453061467) 9600000000000000000),
          (exactRationalLiteral (1075128536333423) 1200000000000000000),
          (exactRationalLiteral (18706016041792723) 19200000000000000000),
          (exactRationalLiteral (69502261004877373) 153600000000000000000),
          (exactRationalLiteral (1349915052917491) 19200000000000000000),
          (exactRationalLiteral (1088294071555303) 640000000000000000),
          (exactRationalLiteral (2010583031569337) 9600000000000000000),
          (exactRationalLiteral (8694269531349133) 960000000000000000),
          (exactRationalLiteral (154706736052762607) 30720000000000000000),
          (exactRationalLiteral (146743193275932389) 30720000000000000000),
          (exactRationalLiteral (964432115875740751) 51200000000000000000),
          (exactRationalLiteral (3245512811811628233) 51200000000000000000),
          (exactRationalLiteral (28588710084215676577) 76800000000000000000),
          (exactRationalLiteral (6412017910475789851) 3200000000000000000),
          (exactRationalLiteral (41483705917704060787) 19200000000000000000),
          (exactRationalLiteral (4151145224154843973) 9600000000000000000),
          (exactRationalLiteral (23012893152665415607) 38400000000000000000),
          (exactRationalLiteral (58270205117400043209) 51200000000000000000),
          (exactRationalLiteral (73449469221263886301) 38400000000000000000),
          (exactRationalLiteral (58270205117400043209) 51200000000000000000),
          (exactRationalLiteral (23012893152665415607) 38400000000000000000),
          (exactRationalLiteral (4151145224154843973) 9600000000000000000),
          (exactRationalLiteral (41483705917704060787) 19200000000000000000),
          (exactRationalLiteral (6412017910475789851) 3200000000000000000),
          (exactRationalLiteral (28588710084215676577) 76800000000000000000),
          (exactRationalLiteral (3245512811811628233) 51200000000000000000),
          (exactRationalLiteral (964432115875740751) 51200000000000000000),
          (exactRationalLiteral (146743193275932389) 30720000000000000000),
          (exactRationalLiteral (154706736052762607) 30720000000000000000),
          (exactRationalLiteral (8694269531349133) 960000000000000000),
          (exactRationalLiteral (2010583031569337) 9600000000000000000),
          (exactRationalLiteral (1088294071555303) 640000000000000000),
          (exactRationalLiteral (1349915052917491) 19200000000000000000),
          (exactRationalLiteral (69502261004877373) 153600000000000000000),
          (exactRationalLiteral (18706016041792723) 19200000000000000000),
          (exactRationalLiteral (1075128536333423) 1200000000000000000),
          (exactRationalLiteral (97435126453061467) 9600000000000000000),
          (exactRationalLiteral (73670223963497773) 3200000000000000000),
          (exactRationalLiteral (774191556766925239) 19200000000000000000),
          (exactRationalLiteral (5685168566763805313) 76800000000000000000),
          (exactRationalLiteral (34930886317647829) 1280000000000000000),
          (exactRationalLiteral (234731138464279751) 38400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 10),
      (37, 18),
      (37, 26),
      (37, 34)
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
            (exactRationalLiteral (910866312816199267) 307200000000000000000),
            (exactRationalLiteral (-82806028437836297) 6400000000000000000),
            (exactRationalLiteral (7527820767076027) 400000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2286124582540624133) 81920000000000000000),
            (exactRationalLiteral (23378340308460819) 5120000000000000000),
            (exactRationalLiteral (-26083335620684793) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-38142710903617881649) 614400000000000000000),
            (exactRationalLiteral (1182392020625514619) 12800000000000000000),
            (exactRationalLiteral (102342279268996439) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (483874863387303923) 38400000000000000000),
            (exactRationalLiteral (-269508965234393269) 1600000000000000000),
            (exactRationalLiteral (-967829843477017) 12500000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (18222544549759921217) 614400000000000000000),
            (exactRationalLiteral (1364083364790499349) 12800000000000000000),
            (exactRationalLiteral (-308773955698139) 160000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2408209793123832421) 204800000000000000000),
            (exactRationalLiteral (-63358755429128711) 2560000000000000000),
            (exactRationalLiteral (15453795047472249) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (36298964526229273) 30720000000000000000),
            (exactRationalLiteral (13608568482346157) 3200000000000000000),
            (exactRationalLiteral (-1186704176661811) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1309730946093679507) 1228800000000000000000),
            (exactRationalLiteral (-36113756778006343) 25600000000000000000),
            (exactRationalLiteral (1711876454418389) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-506571056704236377) 1228800000000000000000),
            (exactRationalLiteral (901191600539039) 5120000000000000000),
            (exactRationalLiteral (-591258406818689) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (92699108767048307) 1228800000000000000000),
            (exactRationalLiteral (2344524198486951) 25600000000000000000),
            (exactRationalLiteral (271101117911051) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1075679150928646927) 614400000000000000000),
            (exactRationalLiteral (2055208802240191) 2560000000000000000),
            (exactRationalLiteral (-6766512793621) 160000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (159109419526327531) 614400000000000000000),
            (exactRationalLiteral (2121851866000203) 2560000000000000000),
            (exactRationalLiteral (463818978250099) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2800673374007737427) 307200000000000000000),
            (exactRationalLiteral (-52122652974123) 51200000000000000),
            (exactRationalLiteral (-348207681076379) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-6083725141458647567) 1228800000000000000000),
            (exactRationalLiteral (14886152275790941) 25600000000000000000),
            (exactRationalLiteral (965519681603929) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4919929111433301653) 1228800000000000000000),
            (exactRationalLiteral (108809413784263087) 25600000000000000000),
            (exactRationalLiteral (186293396346887) 320000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1435001659680096271) 81920000000000000000),
            (exactRationalLiteral (198676863169376963) 25600000000000000000),
            (exactRationalLiteral (5474540338563927) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24378591352239976629) 409600000000000000000),
            (exactRationalLiteral (622763035545956941) 25600000000000000000),
            (exactRationalLiteral (5670377789770869) 320000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-191607132827865656261) 614400000000000000000),
            (exactRationalLiteral (4878929613869759279) 12800000000000000000),
            (exactRationalLiteral (206275905977674963) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (4810451435413466963) 2560000000000000000),
            (exactRationalLiteral (-440999449236840147) 400000000000000000),
            (exactRationalLiteral (-101154295603248513) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-2672957086752681920483) 1228800000000000000000),
            (exactRationalLiteral (1804574480097439337) 25600000000000000000),
            (exactRationalLiteral (7490105196639111301) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (342026110978274239553) 614400000000000000000),
            (exactRationalLiteral (4290071676624765353) 2560000000000000000),
            (exactRationalLiteral (-3860763901747106071) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (72003612884314789049) 307200000000000000000),
            (exactRationalLiteral (-9293928393976916751) 6400000000000000000),
            (exactRationalLiteral (961735157183258393) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-365557176517168162269) 409600000000000000000),
            (exactRationalLiteral (28483673778087521797) 25600000000000000000),
            (exactRationalLiteral (-1563617127284830671) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (493649497594626496841) 307200000000000000000),
            (exactRationalLiteral (-1852048330394077967) 1280000000000000000),
            (exactRationalLiteral (368539657436245553) 400000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-365557176517168162269) 409600000000000000000),
            (exactRationalLiteral (28483673778087521797) 25600000000000000000),
            (exactRationalLiteral (-1563617127284830671) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (72003612884314789049) 307200000000000000000),
            (exactRationalLiteral (-9293928393976916751) 6400000000000000000),
            (exactRationalLiteral (961735157183258393) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (342026110978274239553) 614400000000000000000),
            (exactRationalLiteral (4290071676624765353) 2560000000000000000),
            (exactRationalLiteral (-3860763901747106071) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2672957086752681920483) 1228800000000000000000),
            (exactRationalLiteral (1804574480097439337) 25600000000000000000),
            (exactRationalLiteral (7490105196639111301) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4810451435413466963) 2560000000000000000),
            (exactRationalLiteral (-440999449236840147) 400000000000000000),
            (exactRationalLiteral (-101154295603248513) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-191607132827865656261) 614400000000000000000),
            (exactRationalLiteral (4878929613869759279) 12800000000000000000),
            (exactRationalLiteral (206275905977674963) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-24378591352239976629) 409600000000000000000),
            (exactRationalLiteral (622763035545956941) 25600000000000000000),
            (exactRationalLiteral (5670377789770869) 320000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1435001659680096271) 81920000000000000000),
            (exactRationalLiteral (198676863169376963) 25600000000000000000),
            (exactRationalLiteral (5474540338563927) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4919929111433301653) 1228800000000000000000),
            (exactRationalLiteral (108809413784263087) 25600000000000000000),
            (exactRationalLiteral (186293396346887) 320000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6083725141458647567) 1228800000000000000000),
            (exactRationalLiteral (14886152275790941) 25600000000000000000),
            (exactRationalLiteral (965519681603929) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2800673374007737427) 307200000000000000000),
            (exactRationalLiteral (-52122652974123) 51200000000000000),
            (exactRationalLiteral (-348207681076379) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (159109419526327531) 614400000000000000000),
            (exactRationalLiteral (2121851866000203) 2560000000000000000),
            (exactRationalLiteral (463818978250099) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1075679150928646927) 614400000000000000000),
            (exactRationalLiteral (2055208802240191) 2560000000000000000),
            (exactRationalLiteral (-6766512793621) 160000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (92699108767048307) 1228800000000000000000),
            (exactRationalLiteral (2344524198486951) 25600000000000000000),
            (exactRationalLiteral (271101117911051) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-506571056704236377) 1228800000000000000000),
            (exactRationalLiteral (901191600539039) 5120000000000000000),
            (exactRationalLiteral (-591258406818689) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1309730946093679507) 1228800000000000000000),
            (exactRationalLiteral (-36113756778006343) 25600000000000000000),
            (exactRationalLiteral (1711876454418389) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (36298964526229273) 30720000000000000000),
            (exactRationalLiteral (13608568482346157) 3200000000000000000),
            (exactRationalLiteral (-1186704176661811) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-2408209793123832421) 204800000000000000000),
            (exactRationalLiteral (-63358755429128711) 2560000000000000000),
            (exactRationalLiteral (15453795047472249) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (18222544549759921217) 614400000000000000000),
            (exactRationalLiteral (1364083364790499349) 12800000000000000000),
            (exactRationalLiteral (-308773955698139) 160000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (483874863387303923) 38400000000000000000),
            (exactRationalLiteral (-269508965234393269) 1600000000000000000),
            (exactRationalLiteral (-967829843477017) 12500000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-38142710903617881649) 614400000000000000000),
            (exactRationalLiteral (1182392020625514619) 12800000000000000000),
            (exactRationalLiteral (102342279268996439) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2286124582540624133) 81920000000000000000),
            (exactRationalLiteral (23378340308460819) 5120000000000000000),
            (exactRationalLiteral (-26083335620684793) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (910866312816199267) 307200000000000000000),
            (exactRationalLiteral (-82806028437836297) 6400000000000000000),
            (exactRationalLiteral (7527820767076027) 400000000000000000),
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
          (exactRationalLiteral (143845351598020117) 5120000000000000000),
          (exactRationalLiteral (129258978522301691) 1920000000000000000),
          (exactRationalLiteral (109362967888198493) 4800000000000000000),
          (exactRationalLiteral (2786392859982165731) 76800000000000000000),
          (exactRationalLiteral (1015085986932778393) 76800000000000000000),
          (exactRationalLiteral (1818774729597031) 1280000000000000000),
          (exactRationalLiteral (176500700848264301) 153600000000000000000),
          (exactRationalLiteral (8150013016499669) 19200000000000000000),
          (exactRationalLiteral (4192927535618479) 51200000000000000000),
          (exactRationalLiteral (138299124722549293) 76800000000000000000),
          (exactRationalLiteral (8013518287571587) 25600000000000000000),
          (exactRationalLiteral (352658718008776321) 38400000000000000000),
          (exactRationalLiteral (95708789364054211) 19200000000000000000),
          (exactRationalLiteral (27309387192082643) 6400000000000000000),
          (exactRationalLiteral (345373916103106489) 19200000000000000000),
          (exactRationalLiteral (1170561556431868067) 19200000000000000000),
          (exactRationalLiteral (1070725148046693807) 3200000000000000000),
          (exactRationalLiteral (4655235795056692489) 2400000000000000000),
          (exactRationalLiteral (27949948773952244639) 12800000000000000000),
          (exactRationalLiteral (16467264341673159517) 25600000000000000000),
          (exactRationalLiteral (33483960540457921) 100000000000000000),
          (exactRationalLiteral (18545835953734027847) 19200000000000000000),
          (exactRationalLiteral (2721666904258068159) 1600000000000000000),
          (exactRationalLiteral (18545835953734027847) 19200000000000000000),
          (exactRationalLiteral (33483960540457921) 100000000000000000),
          (exactRationalLiteral (16467264341673159517) 25600000000000000000),
          (exactRationalLiteral (27949948773952244639) 12800000000000000000),
          (exactRationalLiteral (4655235795056692489) 2400000000000000000),
          (exactRationalLiteral (1070725148046693807) 3200000000000000000),
          (exactRationalLiteral (1170561556431868067) 19200000000000000000),
          (exactRationalLiteral (345373916103106489) 19200000000000000000),
          (exactRationalLiteral (27309387192082643) 6400000000000000000),
          (exactRationalLiteral (95708789364054211) 19200000000000000000),
          (exactRationalLiteral (352658718008776321) 38400000000000000000),
          (exactRationalLiteral (8013518287571587) 25600000000000000000),
          (exactRationalLiteral (138299124722549293) 76800000000000000000),
          (exactRationalLiteral (4192927535618479) 51200000000000000000),
          (exactRationalLiteral (8150013016499669) 19200000000000000000),
          (exactRationalLiteral (176500700848264301) 153600000000000000000),
          (exactRationalLiteral (1818774729597031) 1280000000000000000),
          (exactRationalLiteral (1015085986932778393) 76800000000000000000),
          (exactRationalLiteral (2786392859982165731) 76800000000000000000),
          (exactRationalLiteral (109362967888198493) 4800000000000000000),
          (exactRationalLiteral (129258978522301691) 1920000000000000000),
          (exactRationalLiteral (143845351598020117) 5120000000000000000),
          (exactRationalLiteral (6159126082153113) 1600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 9),
      (37, 17),
      (37, 25),
      (37, 33)
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
            (exactRationalLiteral (166296404218134051) 102400000000000000000),
            (exactRationalLiteral (-55432134739378017) 6400000000000000000),
            (exactRationalLiteral (6159126082153113) 400000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2237237378930946319) 81920000000000000000),
            (exactRationalLiteral (-67920814790068773) 5120000000000000000),
            (exactRationalLiteral (-19566241928580003) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-29980147433043997219) 614400000000000000000),
            (exactRationalLiteral (1511813135497920099) 12800000000000000000),
            (exactRationalLiteral (62368278167206301) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-44767873088764909) 4800000000000000000),
            (exactRationalLiteral (-57502928026600877) 320000000000000000),
            (exactRationalLiteral (-630099350744711) 50000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (8745452353884019441) 204800000000000000000),
            (exactRationalLiteral (256365453184410249) 2560000000000000000),
            (exactRationalLiteral (-39584179655733357) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8876255060045419309) 614400000000000000000),
            (exactRationalLiteral (-223132876140618411) 12800000000000000000),
            (exactRationalLiteral (31376655455040323) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (244846199432836111) 153600000000000000000),
            (exactRationalLiteral (6831959789476181) 3200000000000000000),
            (exactRationalLiteral (-2201600169773177) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1498423127082065209) 1228800000000000000000),
            (exactRationalLiteral (-25542329847016943) 25600000000000000000),
            (exactRationalLiteral (3573837011076311) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-488725392584283179) 1228800000000000000000),
            (exactRationalLiteral (1093432868223587) 25600000000000000000),
            (exactRationalLiteral (-223000832083423) 320000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (110693676481712089) 1228800000000000000000),
            (exactRationalLiteral (3766033224535887) 25600000000000000000),
            (exactRationalLiteral (439653395113417) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (378942374769542111) 204800000000000000000),
            (exactRationalLiteral (10089563795524003) 12800000000000000000),
            (exactRationalLiteral (-59407543870371) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (228297078850432529) 614400000000000000000),
            (exactRationalLiteral (12447673045550271) 12800000000000000000),
            (exactRationalLiteral (455387879524529) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2843989873142829257) 307200000000000000000),
            (exactRationalLiteral (-7931170961862407) 6400000000000000000),
            (exactRationalLiteral (-359711988972137) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1196763630231713513) 245760000000000000000),
            (exactRationalLiteral (18250151235250261) 25600000000000000000),
            (exactRationalLiteral (716479798125731) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-283811994175671409) 81920000000000000000),
            (exactRationalLiteral (22378567573424043) 5120000000000000000),
            (exactRationalLiteral (610245059694129) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20272879096882958179) 1228800000000000000000),
            (exactRationalLiteral (217770092143361163) 25600000000000000000),
            (exactRationalLiteral (4072074148428173) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-69083516255031387197) 1228800000000000000000),
            (exactRationalLiteral (723899051854648773) 25600000000000000000),
            (exactRationalLiteral (22216119205491571) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-53408389495176195717) 204800000000000000000),
            (exactRationalLiteral (5520571131473666071) 12800000000000000000),
            (exactRationalLiteral (114544852824278433) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (65775187544370700237) 38400000000000000000),
            (exactRationalLiteral (-122448560526179449) 80000000000000000),
            (exactRationalLiteral (-14017811558161717) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-2579794904472404062633) 1228800000000000000000),
            (exactRationalLiteral (27991731786665827649) 25600000000000000000),
            (exactRationalLiteral (1120694691329016571) 320000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (17110187707122533659) 24576000000000000000),
            (exactRationalLiteral (7685101887141109573) 12800000000000000000),
            (exactRationalLiteral (-120874573849770101) 32000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9014626155573679537) 102400000000000000000),
            (exactRationalLiteral (-5815480735209558503) 6400000000000000000),
            (exactRationalLiteral (777488672200420731) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-943572102239547420101) 1228800000000000000000),
            (exactRationalLiteral (22709600354373151101) 25600000000000000000),
            (exactRationalLiteral (-1323419584572354677) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (147438963604805878761) 102400000000000000000),
            (exactRationalLiteral (-1576579880207228343) 1280000000000000000),
            (exactRationalLiteral (320131468030878507) 400000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-943572102239547420101) 1228800000000000000000),
            (exactRationalLiteral (22709600354373151101) 25600000000000000000),
            (exactRationalLiteral (-1323419584572354677) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9014626155573679537) 102400000000000000000),
            (exactRationalLiteral (-5815480735209558503) 6400000000000000000),
            (exactRationalLiteral (777488672200420731) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (17110187707122533659) 24576000000000000000),
            (exactRationalLiteral (7685101887141109573) 12800000000000000000),
            (exactRationalLiteral (-120874573849770101) 32000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2579794904472404062633) 1228800000000000000000),
            (exactRationalLiteral (27991731786665827649) 25600000000000000000),
            (exactRationalLiteral (1120694691329016571) 320000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (65775187544370700237) 38400000000000000000),
            (exactRationalLiteral (-122448560526179449) 80000000000000000),
            (exactRationalLiteral (-14017811558161717) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-53408389495176195717) 204800000000000000000),
            (exactRationalLiteral (5520571131473666071) 12800000000000000000),
            (exactRationalLiteral (114544852824278433) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-69083516255031387197) 1228800000000000000000),
            (exactRationalLiteral (723899051854648773) 25600000000000000000),
            (exactRationalLiteral (22216119205491571) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20272879096882958179) 1228800000000000000000),
            (exactRationalLiteral (217770092143361163) 25600000000000000000),
            (exactRationalLiteral (4072074148428173) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-283811994175671409) 81920000000000000000),
            (exactRationalLiteral (22378567573424043) 5120000000000000000),
            (exactRationalLiteral (610245059694129) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1196763630231713513) 245760000000000000000),
            (exactRationalLiteral (18250151235250261) 25600000000000000000),
            (exactRationalLiteral (716479798125731) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2843989873142829257) 307200000000000000000),
            (exactRationalLiteral (-7931170961862407) 6400000000000000000),
            (exactRationalLiteral (-359711988972137) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (228297078850432529) 614400000000000000000),
            (exactRationalLiteral (12447673045550271) 12800000000000000000),
            (exactRationalLiteral (455387879524529) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (378942374769542111) 204800000000000000000),
            (exactRationalLiteral (10089563795524003) 12800000000000000000),
            (exactRationalLiteral (-59407543870371) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (110693676481712089) 1228800000000000000000),
            (exactRationalLiteral (3766033224535887) 25600000000000000000),
            (exactRationalLiteral (439653395113417) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-488725392584283179) 1228800000000000000000),
            (exactRationalLiteral (1093432868223587) 25600000000000000000),
            (exactRationalLiteral (-223000832083423) 320000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1498423127082065209) 1228800000000000000000),
            (exactRationalLiteral (-25542329847016943) 25600000000000000000),
            (exactRationalLiteral (3573837011076311) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (244846199432836111) 153600000000000000000),
            (exactRationalLiteral (6831959789476181) 3200000000000000000),
            (exactRationalLiteral (-2201600169773177) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-8876255060045419309) 614400000000000000000),
            (exactRationalLiteral (-223132876140618411) 12800000000000000000),
            (exactRationalLiteral (31376655455040323) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8745452353884019441) 204800000000000000000),
            (exactRationalLiteral (256365453184410249) 2560000000000000000),
            (exactRationalLiteral (-39584179655733357) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-44767873088764909) 4800000000000000000),
            (exactRationalLiteral (-57502928026600877) 320000000000000000),
            (exactRationalLiteral (-630099350744711) 50000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-29980147433043997219) 614400000000000000000),
            (exactRationalLiteral (1511813135497920099) 12800000000000000000),
            (exactRationalLiteral (62368278167206301) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2237237378930946319) 81920000000000000000),
            (exactRationalLiteral (-67920814790068773) 5120000000000000000),
            (exactRationalLiteral (-19566241928580003) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (166296404218134051) 102400000000000000000),
            (exactRationalLiteral (-55432134739378017) 6400000000000000000),
            (exactRationalLiteral (6159126082153113) 400000000000000000),
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
          (exactRationalLiteral (684347342461457) 307200000000000000),
          (exactRationalLiteral (285563221188802203) 10240000000000000000),
          (exactRationalLiteral (4288561875560655443) 76800000000000000000),
          (exactRationalLiteral (24677644779696197) 1200000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (61886103849175759) 153600000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (251512276897008419) 51200000000000000000),
          (exactRationalLiteral (114771677002408231) 30720000000000000000),
          (exactRationalLiteral (2614158989721586159) 153600000000000000000),
          (exactRationalLiteral (8898187146013397177) 153600000000000000000),
          (exactRationalLiteral (881986908974500259) 3072000000000000000),
          (exactRationalLiteral (17305711141969359497) 9600000000000000000),
          (exactRationalLiteral (110250681816352886783) 51200000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (5864363741430299393) 38400000000000000000),
          (exactRationalLiteral (126973907603467521929) 153600000000000000000),
          (exactRationalLiteral (58368773439540172559) 38400000000000000000),
          (exactRationalLiteral (126973907603467521929) 153600000000000000000),
          (exactRationalLiteral (5864363741430299393) 38400000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (110250681816352886783) 51200000000000000000),
          (exactRationalLiteral (17305711141969359497) 9600000000000000000),
          (exactRationalLiteral (881986908974500259) 3072000000000000000),
          (exactRationalLiteral (8898187146013397177) 153600000000000000000),
          (exactRationalLiteral (2614158989721586159) 153600000000000000000),
          (exactRationalLiteral (114771677002408231) 30720000000000000000),
          (exactRationalLiteral (251512276897008419) 51200000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (61886103849175759) 153600000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (24677644779696197) 1200000000000000000),
          (exactRationalLiteral (4288561875560655443) 76800000000000000000),
          (exactRationalLiteral (285563221188802203) 10240000000000000000),
          (exactRationalLiteral (684347342461457) 307200000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 8),
      (37, 16),
      (37, 24),
      (37, 32)
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
            (exactRationalLiteral (234731138464279751) 307200000000000000000),
            (exactRationalLiteral (-33533019780611393) 6400000000000000000),
            (exactRationalLiteral (4790431397230199) 400000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2031820239892628481) 81920000000000000000),
            (exactRationalLiteral (-26630319024035841) 1024000000000000000),
            (exactRationalLiteral (-13049148236475213) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-4064149057291432313) 122880000000000000000),
            (exactRationalLiteral (1681338245963165027) 12800000000000000000),
            (exactRationalLiteral (22394277065416163) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-405094405741805177) 12800000000000000000),
            (exactRationalLiteral (-55918110969261729) 320000000000000000),
            (exactRationalLiteral (1305560336209323) 25000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (33300149261806594861) 614400000000000000000),
            (exactRationalLiteral (1047409927544632493) 12800000000000000000),
            (exactRationalLiteral (-77624489532976019) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9774841009798373603) 614400000000000000000),
            (exactRationalLiteral (-65780533505320971) 12800000000000000000),
            (exactRationalLiteral (47299515862608397) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (85119724053323203) 51200000000000000000),
            (exactRationalLiteral (-4004232875839259) 3200000000000000000),
            (exactRationalLiteral (-3216496162884543) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1601343219804619447) 1228800000000000000000),
            (exactRationalLiteral (-1504612137879171) 5120000000000000000),
            (exactRationalLiteral (5435797567734233) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-497639828314340741) 1228800000000000000000),
            (exactRationalLiteral (-176563011225669) 1024000000000000000),
            (exactRationalLiteral (-1638749914015541) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (46413308559699293) 409600000000000000000),
            (exactRationalLiteral (5861751359394287) 25600000000000000000),
            (exactRationalLiteral (608205672315783) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (239309863327143367) 122880000000000000000),
            (exactRationalLiteral (9800783660237987) 12800000000000000000),
            (exactRationalLiteral (-84982523772637) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (102804682427708741) 204800000000000000000),
            (exactRationalLiteral (14252362366197247) 12800000000000000000),
            (exactRationalLiteral (446956780798959) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-23167515680106019) 2457600000000000000),
            (exactRationalLiteral (-9393027533542471) 6400000000000000000),
            (exactRationalLiteral (-74243259373579) 80000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1955571881901156673) 409600000000000000000),
            (exactRationalLiteral (20617990660796789) 25600000000000000000),
            (exactRationalLiteral (467439914647533) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3579784832404181521) 1228800000000000000000),
            (exactRationalLiteral (113691374261816119) 25600000000000000000),
            (exactRationalLiteral (289023137653823) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18923003519002196141) 1228800000000000000000),
            (exactRationalLiteral (231253456356802347) 25600000000000000000),
            (exactRationalLiteral (2669607958292419) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-64498071592411046803) 1228800000000000000000),
            (exactRationalLiteral (800491989189889509) 25600000000000000000),
            (exactRationalLiteral (16080349462128797) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-126094127675408835649) 614400000000000000000),
            (exactRationalLiteral (5795288436463986743) 12800000000000000000),
            (exactRationalLiteral (22813799670881903) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (57711466170559989989) 38400000000000000000),
            (exactRationalLiteral (-721355680400074487) 400000000000000000),
            (exactRationalLiteral (-39023819978368657) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-784049786410881405421) 409600000000000000000),
            (exactRationalLiteral (46632362133258102177) 25600000000000000000),
            (exactRationalLiteral (3716841716651054409) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (146986176689330127599) 204800000000000000000),
            (exactRationalLiteral (-544911277366038687) 2560000000000000000),
            (exactRationalLiteral (-2182964790741398979) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (743872181937385717) 307200000000000000000),
            (exactRationalLiteral (-3074019016373550903) 6400000000000000000),
            (exactRationalLiteral (593242187217583069) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-822234744957326865643) 1228800000000000000000),
            (exactRationalLiteral (17896317101508684381) 25600000000000000000),
            (exactRationalLiteral (-1083222041859878683) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (398667439266949859893) 307200000000000000000),
            (exactRationalLiteral (-6699189907723361779) 6400000000000000000),
            (exactRationalLiteral (271723278625511461) 400000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-822234744957326865643) 1228800000000000000000),
            (exactRationalLiteral (17896317101508684381) 25600000000000000000),
            (exactRationalLiteral (-1083222041859878683) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (743872181937385717) 307200000000000000000),
            (exactRationalLiteral (-3074019016373550903) 6400000000000000000),
            (exactRationalLiteral (593242187217583069) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (146986176689330127599) 204800000000000000000),
            (exactRationalLiteral (-544911277366038687) 2560000000000000000),
            (exactRationalLiteral (-2182964790741398979) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-784049786410881405421) 409600000000000000000),
            (exactRationalLiteral (46632362133258102177) 25600000000000000000),
            (exactRationalLiteral (3716841716651054409) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (57711466170559989989) 38400000000000000000),
            (exactRationalLiteral (-721355680400074487) 400000000000000000),
            (exactRationalLiteral (-39023819978368657) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-126094127675408835649) 614400000000000000000),
            (exactRationalLiteral (5795288436463986743) 12800000000000000000),
            (exactRationalLiteral (22813799670881903) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-64498071592411046803) 1228800000000000000000),
            (exactRationalLiteral (800491989189889509) 25600000000000000000),
            (exactRationalLiteral (16080349462128797) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18923003519002196141) 1228800000000000000000),
            (exactRationalLiteral (231253456356802347) 25600000000000000000),
            (exactRationalLiteral (2669607958292419) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3579784832404181521) 1228800000000000000000),
            (exactRationalLiteral (113691374261816119) 25600000000000000000),
            (exactRationalLiteral (289023137653823) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1955571881901156673) 409600000000000000000),
            (exactRationalLiteral (20617990660796789) 25600000000000000000),
            (exactRationalLiteral (467439914647533) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23167515680106019) 2457600000000000000),
            (exactRationalLiteral (-9393027533542471) 6400000000000000000),
            (exactRationalLiteral (-74243259373579) 80000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (102804682427708741) 204800000000000000000),
            (exactRationalLiteral (14252362366197247) 12800000000000000000),
            (exactRationalLiteral (446956780798959) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (239309863327143367) 122880000000000000000),
            (exactRationalLiteral (9800783660237987) 12800000000000000000),
            (exactRationalLiteral (-84982523772637) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (46413308559699293) 409600000000000000000),
            (exactRationalLiteral (5861751359394287) 25600000000000000000),
            (exactRationalLiteral (608205672315783) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-497639828314340741) 1228800000000000000000),
            (exactRationalLiteral (-176563011225669) 1024000000000000000),
            (exactRationalLiteral (-1638749914015541) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1601343219804619447) 1228800000000000000000),
            (exactRationalLiteral (-1504612137879171) 5120000000000000000),
            (exactRationalLiteral (5435797567734233) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (85119724053323203) 51200000000000000000),
            (exactRationalLiteral (-4004232875839259) 3200000000000000000),
            (exactRationalLiteral (-3216496162884543) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-9774841009798373603) 614400000000000000000),
            (exactRationalLiteral (-65780533505320971) 12800000000000000000),
            (exactRationalLiteral (47299515862608397) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (33300149261806594861) 614400000000000000000),
            (exactRationalLiteral (1047409927544632493) 12800000000000000000),
            (exactRationalLiteral (-77624489532976019) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-405094405741805177) 12800000000000000000),
            (exactRationalLiteral (-55918110969261729) 320000000000000000),
            (exactRationalLiteral (1305560336209323) 25000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-4064149057291432313) 122880000000000000000),
            (exactRationalLiteral (1681338245963165027) 12800000000000000000),
            (exactRationalLiteral (22394277065416163) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2031820239892628481) 81920000000000000000),
            (exactRationalLiteral (-26630319024035841) 1024000000000000000),
            (exactRationalLiteral (-13049148236475213) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (234731138464279751) 307200000000000000000),
            (exactRationalLiteral (-33533019780611393) 6400000000000000000),
            (exactRationalLiteral (4790431397230199) 400000000000000000),
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
          (exactRationalLiteral (812607538733020441) 19200000000000000000),
          (exactRationalLiteral (1507936892537622623) 25600000000000000000),
          (exactRationalLiteral (309246327792815219) 19200000000000000000),
          (exactRationalLiteral (682480346880567) 400000000000000000),
          (exactRationalLiteral (16825344357709151) 12800000000000000000),
          (exactRationalLiteral (64507522096888969) 153600000000000000000),
          (exactRationalLiteral (19841759114103659) 153600000000000000000),
          (exactRationalLiteral (51070163856465073) 25600000000000000000),
          (exactRationalLiteral (44063473646844007) 76800000000000000000),
          (exactRationalLiteral (365654742957303919) 38400000000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (3486605476744635953) 4800000000000000000),
          (exactRationalLiteral (46241324356258619) 1200000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (819539810391990553) 600000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (46241324356258619) 1200000000000000000),
          (exactRationalLiteral (3486605476744635953) 4800000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (365654742957303919) 38400000000000000000),
          (exactRationalLiteral (44063473646844007) 76800000000000000000),
          (exactRationalLiteral (51070163856465073) 25600000000000000000),
          (exactRationalLiteral (19841759114103659) 153600000000000000000),
          (exactRationalLiteral (64507522096888969) 153600000000000000000),
          (exactRationalLiteral (16825344357709151) 12800000000000000000),
          (exactRationalLiteral (682480346880567) 400000000000000000),
          (exactRationalLiteral (309246327792815219) 19200000000000000000),
          (exactRationalLiteral (1507936892537622623) 25600000000000000000),
          (exactRationalLiteral (812607538733020441) 19200000000000000000),
          (exactRationalLiteral (12342573336230231) 300000000000000000),
          (exactRationalLiteral (4200852547840459) 160000000000000000),
          (exactRationalLiteral (684347342461457) 600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 7),
      (37, 15),
      (37, 23),
      (37, 31)
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
            (exactRationalLiteral (684347342461457) 2457600000000000000),
            (exactRationalLiteral (-684347342461457) 256000000000000000),
            (exactRationalLiteral (684347342461457) 80000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1722009914962508939) 81920000000000000000),
            (exactRationalLiteral (-172314000681870477) 5120000000000000000),
            (exactRationalLiteral (-6532054544370423) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-10123880490300337999) 614400000000000000000),
            (exactRationalLiteral (1690967352021249403) 12800000000000000000),
            (exactRationalLiteral (-703188961454959) 32000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1004878276801332143) 19200000000000000000),
            (exactRationalLiteral (-245736709374306049) 1600000000000000000),
            (exactRationalLiteral (5852340695582003) 50000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (38500953713169706943) 614400000000000000000),
            (exactRationalLiteral (660831349658243093) 12800000000000000000),
            (exactRationalLiteral (-115664799410218681) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3179412859616242123) 204800000000000000000),
            (exactRationalLiteral (31052650152049753) 2560000000000000000),
            (exactRationalLiteral (63222376270176471) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7547049479114963) 6144000000000000000),
            (exactRationalLiteral (-18900009513600163) 3200000000000000000),
            (exactRationalLiteral (-4231392155995909) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1573804170901552093) 1228800000000000000000),
            (exactRationalLiteral (17944050694856921) 25600000000000000000),
            (exactRationalLiteral (1459551624878431) 320000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-545884261980771287) 1228800000000000000000),
            (exactRationalLiteral (-12016566443900741) 25600000000000000000),
            (exactRationalLiteral (-2162495667613967) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (182383111012062461) 1228800000000000000000),
            (exactRationalLiteral (8631678603062151) 25600000000000000000),
            (exactRationalLiteral (776757949518149) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1254231928392264049) 614400000000000000000),
            (exactRationalLiteral (9409703605342907) 12800000000000000000),
            (exactRationalLiteral (-110557503674903) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (399257978454994933) 614400000000000000000),
            (exactRationalLiteral (16023327291941943) 12800000000000000000),
            (exactRationalLiteral (438525682073389) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2956798238008504973) 307200000000000000000),
            (exactRationalLiteral (-10900901336805567) 6400000000000000000),
            (exactRationalLiteral (-382720604763653) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-5738394582296831681) 1228800000000000000000),
            (exactRationalLiteral (879586822097221) 1024000000000000000),
            (exactRationalLiteral (43680006233867) 320000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-579090639373920031) 245760000000000000000),
            (exactRationalLiteral (114205022968350799) 25600000000000000000),
            (exactRationalLiteral (-32198784386483) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5836352450040805349) 409600000000000000000),
            (exactRationalLiteral (47825391161940103) 5120000000000000000),
            (exactRationalLiteral (253428353631333) 320000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19842232847566538427) 409600000000000000000),
            (exactRationalLiteral (852541847551679149) 25600000000000000000),
            (exactRationalLiteral (9944579718766023) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3656622226927516739) 24576000000000000000),
            (exactRationalLiteral (1140616305768144259) 2560000000000000000),
            (exactRationalLiteral (-68917253482514627) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (16237057705756143991) 12800000000000000000),
            (exactRationalLiteral (-768338082544371873) 400000000000000000),
            (exactRationalLiteral (-7958582165928729) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-2035299612793259064077) 1228800000000000000000),
            (exactRationalLiteral (57726465519874262921) 25600000000000000000),
            (exactRationalLiteral (1830209976657025963) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (401771212480123848623) 614400000000000000000),
            (exactRationalLiteral (-9778616438790082259) 12800000000000000000),
            (exactRationalLiteral (-1344065235238545433) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-11318321609624273521) 307200000000000000000),
            (exactRationalLiteral (-1069543237468893951) 6400000000000000000),
            (exactRationalLiteral (408995702234745407) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-242298238893247799859) 409600000000000000000),
            (exactRationalLiteral (14043824019494121637) 25600000000000000000),
            (exactRationalLiteral (-843024499147402689) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (361539346406494358567) 307200000000000000000),
            (exactRationalLiteral (-5709113172032050027) 6400000000000000000),
            (exactRationalLiteral (44663017844028883) 80000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-242298238893247799859) 409600000000000000000),
            (exactRationalLiteral (14043824019494121637) 25600000000000000000),
            (exactRationalLiteral (-843024499147402689) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11318321609624273521) 307200000000000000000),
            (exactRationalLiteral (-1069543237468893951) 6400000000000000000),
            (exactRationalLiteral (408995702234745407) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (401771212480123848623) 614400000000000000000),
            (exactRationalLiteral (-9778616438790082259) 12800000000000000000),
            (exactRationalLiteral (-1344065235238545433) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2035299612793259064077) 1228800000000000000000),
            (exactRationalLiteral (57726465519874262921) 25600000000000000000),
            (exactRationalLiteral (1830209976657025963) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16237057705756143991) 12800000000000000000),
            (exactRationalLiteral (-768338082544371873) 400000000000000000),
            (exactRationalLiteral (-7958582165928729) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-3656622226927516739) 24576000000000000000),
            (exactRationalLiteral (1140616305768144259) 2560000000000000000),
            (exactRationalLiteral (-68917253482514627) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-19842232847566538427) 409600000000000000000),
            (exactRationalLiteral (852541847551679149) 25600000000000000000),
            (exactRationalLiteral (9944579718766023) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5836352450040805349) 409600000000000000000),
            (exactRationalLiteral (47825391161940103) 5120000000000000000),
            (exactRationalLiteral (253428353631333) 320000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-579090639373920031) 245760000000000000000),
            (exactRationalLiteral (114205022968350799) 25600000000000000000),
            (exactRationalLiteral (-32198784386483) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5738394582296831681) 1228800000000000000000),
            (exactRationalLiteral (879586822097221) 1024000000000000000),
            (exactRationalLiteral (43680006233867) 320000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2956798238008504973) 307200000000000000000),
            (exactRationalLiteral (-10900901336805567) 6400000000000000000),
            (exactRationalLiteral (-382720604763653) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (399257978454994933) 614400000000000000000),
            (exactRationalLiteral (16023327291941943) 12800000000000000000),
            (exactRationalLiteral (438525682073389) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1254231928392264049) 614400000000000000000),
            (exactRationalLiteral (9409703605342907) 12800000000000000000),
            (exactRationalLiteral (-110557503674903) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (182383111012062461) 1228800000000000000000),
            (exactRationalLiteral (8631678603062151) 25600000000000000000),
            (exactRationalLiteral (776757949518149) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-545884261980771287) 1228800000000000000000),
            (exactRationalLiteral (-12016566443900741) 25600000000000000000),
            (exactRationalLiteral (-2162495667613967) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1573804170901552093) 1228800000000000000000),
            (exactRationalLiteral (17944050694856921) 25600000000000000000),
            (exactRationalLiteral (1459551624878431) 320000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7547049479114963) 6144000000000000000),
            (exactRationalLiteral (-18900009513600163) 3200000000000000000),
            (exactRationalLiteral (-4231392155995909) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-3179412859616242123) 204800000000000000000),
            (exactRationalLiteral (31052650152049753) 2560000000000000000),
            (exactRationalLiteral (63222376270176471) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (38500953713169706943) 614400000000000000000),
            (exactRationalLiteral (660831349658243093) 12800000000000000000),
            (exactRationalLiteral (-115664799410218681) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1004878276801332143) 19200000000000000000),
            (exactRationalLiteral (-245736709374306049) 1600000000000000000),
            (exactRationalLiteral (5852340695582003) 50000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-10123880490300337999) 614400000000000000000),
            (exactRationalLiteral (1690967352021249403) 12800000000000000000),
            (exactRationalLiteral (-703188961454959) 32000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1722009914962508939) 81920000000000000000),
            (exactRationalLiteral (-172314000681870477) 5120000000000000000),
            (exactRationalLiteral (-6532054544370423) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 2457600000000000000),
            (exactRationalLiteral (-684347342461457) 256000000000000000),
            (exactRationalLiteral (684347342461457) 80000000000000000),
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
          (exactRationalLiteral (6159126082153113) 12800000000000000000),
          (exactRationalLiteral (235838209852248941) 10240000000000000000),
          (exactRationalLiteral (1903691839740289133) 76800000000000000000),
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (1227790329065340911) 76800000000000000000),
          (exactRationalLiteral (5829738426181063) 3840000000000000000),
          (exactRationalLiteral (200834253611409419) 153600000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (725447984239859519) 153600000000000000000),
          (exactRationalLiteral (134916843798616327) 51200000000000000000),
          (exactRationalLiteral (455548388978799493) 30720000000000000000),
          (exactRationalLiteral (7756427807665834159) 153600000000000000000),
          (exactRationalLiteral (4528570270565871999) 25600000000000000000),
          (exactRationalLiteral (2664089662356532853) 1920000000000000000),
          (exactRationalLiteral (275255632944114220091) 153600000000000000000),
          (exactRationalLiteral (53331927039128379041) 76800000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (96459420125878026319) 153600000000000000000),
          (exactRationalLiteral (15806701470206401059) 12800000000000000000),
          (exactRationalLiteral (96459420125878026319) 153600000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (53331927039128379041) 76800000000000000000),
          (exactRationalLiteral (275255632944114220091) 153600000000000000000),
          (exactRationalLiteral (2664089662356532853) 1920000000000000000),
          (exactRationalLiteral (4528570270565871999) 25600000000000000000),
          (exactRationalLiteral (7756427807665834159) 153600000000000000000),
          (exactRationalLiteral (455548388978799493) 30720000000000000000),
          (exactRationalLiteral (134916843798616327) 51200000000000000000),
          (exactRationalLiteral (725447984239859519) 153600000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (200834253611409419) 153600000000000000000),
          (exactRationalLiteral (5829738426181063) 3840000000000000000),
          (exactRationalLiteral (1227790329065340911) 76800000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (1903691839740289133) 76800000000000000000),
          (exactRationalLiteral (235838209852248941) 10240000000000000000),
          (exactRationalLiteral (6159126082153113) 12800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 6),
      (37, 14),
      (37, 22),
      (37, 30)
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
            (exactRationalLiteral (6159126082153113) 102400000000000000000),
            (exactRationalLiteral (-6159126082153113) 6400000000000000000),
            (exactRationalLiteral (2053042027384371) 400000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1359943153677426013) 81920000000000000000),
            (exactRationalLiteral (-185408031475142589) 5120000000000000000),
            (exactRationalLiteral (-14960852265633) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-348929071016489833) 614400000000000000000),
            (exactRationalLiteral (1540700453672173227) 12800000000000000000),
            (exactRationalLiteral (-57553725138164113) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2663773713285944969) 38400000000000000000),
            (exactRationalLiteral (-185953103716996597) 1600000000000000000),
            (exactRationalLiteral (113669508984317) 625000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (13641934326229190227) 204800000000000000000),
            (exactRationalLiteral (24418306452576609) 2560000000000000000),
            (exactRationalLiteral (-153705109287461343) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7784299117414843831) 614400000000000000000),
            (exactRationalLiteral (439998476656090797) 12800000000000000000),
            (exactRationalLiteral (15829047335548909) 160000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (817595602075069) 6144000000000000000),
            (exactRationalLiteral (-37855370123806531) 3200000000000000000),
            (exactRationalLiteral (-209851525964291) 8000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1371118927013073019) 1228800000000000000000),
            (exactRationalLiteral (10171800861148277) 5120000000000000000),
            (exactRationalLiteral (9159718681050077) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-646028591669937041) 1228800000000000000000),
            (exactRationalLiteral (-21714040621553461) 25600000000000000000),
            (exactRationalLiteral (-2686241421212393) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (244168487133462619) 1228800000000000000000),
            (exactRationalLiteral (12075814955539479) 25600000000000000000),
            (exactRationalLiteral (189062045344103) 320000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (436420386686871197) 204800000000000000000),
            (exactRationalLiteral (8916323630838763) 12800000000000000000),
            (exactRationalLiteral (-136132483577169) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (500626525996624979) 614400000000000000000),
            (exactRationalLiteral (17760567822784359) 12800000000000000000),
            (exactRationalLiteral (430094583347819) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3026842310518085243) 307200000000000000000),
            (exactRationalLiteral (-2490958474330339) 1280000000000000000),
            (exactRationalLiteral (-394224912659411) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-5604831918142129303) 1228800000000000000000),
            (exactRationalLiteral (22365190910151469) 25600000000000000000),
            (exactRationalLiteral (-30639852308863) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-737298110720098127) 409600000000000000000),
            (exactRationalLiteral (22686756797344851) 5120000000000000000),
            (exactRationalLiteral (-353420706426789) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16064699778806875993) 1228800000000000000000),
            (exactRationalLiteral (241390590502055667) 25600000000000000000),
            (exactRationalLiteral (-135324421979089) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-54316655579737799207) 1228800000000000000000),
            (exactRationalLiteral (880048626940017693) 25600000000000000000),
            (exactRationalLiteral (3808809975403249) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19463665918182450783) 204800000000000000000),
            (exactRationalLiteral (5243950408603869727) 12800000000000000000),
            (exactRationalLiteral (-160648306635911157) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (39519874091994584461) 38400000000000000000),
            (exactRationalLiteral (-753190009063789403) 400000000000000000),
            (exactRationalLiteral (23106655646511199) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-1674524826914105288779) 1228800000000000000000),
            (exactRationalLiteral (61274041946514309881) 25600000000000000000),
            (exactRationalLiteral (-56421763337002483) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (330326329246532224057) 614400000000000000000),
            (exactRationalLiteral (-13477078268738556899) 12800000000000000000),
            (exactRationalLiteral (-505165679735691887) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4521539515850680997) 102400000000000000000),
            (exactRationalLiteral (197946601504412353) 6400000000000000000),
            (exactRationalLiteral (44949843450381549) 80000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-651787276381697598047) 1228800000000000000000),
            (exactRationalLiteral (11152121108329462869) 25600000000000000000),
            (exactRationalLiteral (-120565391286985339) 320000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (109923605229107441067) 102400000000000000000),
            (exactRationalLiteral (-4912669193962206459) 6400000000000000000),
            (exactRationalLiteral (174906899814777369) 400000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-651787276381697598047) 1228800000000000000000),
            (exactRationalLiteral (11152121108329462869) 25600000000000000000),
            (exactRationalLiteral (-120565391286985339) 320000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4521539515850680997) 102400000000000000000),
            (exactRationalLiteral (197946601504412353) 6400000000000000000),
            (exactRationalLiteral (44949843450381549) 80000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (330326329246532224057) 614400000000000000000),
            (exactRationalLiteral (-13477078268738556899) 12800000000000000000),
            (exactRationalLiteral (-505165679735691887) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1674524826914105288779) 1228800000000000000000),
            (exactRationalLiteral (61274041946514309881) 25600000000000000000),
            (exactRationalLiteral (-56421763337002483) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (39519874091994584461) 38400000000000000000),
            (exactRationalLiteral (-753190009063789403) 400000000000000000),
            (exactRationalLiteral (23106655646511199) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-19463665918182450783) 204800000000000000000),
            (exactRationalLiteral (5243950408603869727) 12800000000000000000),
            (exactRationalLiteral (-160648306635911157) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-54316655579737799207) 1228800000000000000000),
            (exactRationalLiteral (880048626940017693) 25600000000000000000),
            (exactRationalLiteral (3808809975403249) 1600000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16064699778806875993) 1228800000000000000000),
            (exactRationalLiteral (241390590502055667) 25600000000000000000),
            (exactRationalLiteral (-135324421979089) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-737298110720098127) 409600000000000000000),
            (exactRationalLiteral (22686756797344851) 5120000000000000000),
            (exactRationalLiteral (-353420706426789) 1600000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5604831918142129303) 1228800000000000000000),
            (exactRationalLiteral (22365190910151469) 25600000000000000000),
            (exactRationalLiteral (-30639852308863) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3026842310518085243) 307200000000000000000),
            (exactRationalLiteral (-2490958474330339) 1280000000000000000),
            (exactRationalLiteral (-394224912659411) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (500626525996624979) 614400000000000000000),
            (exactRationalLiteral (17760567822784359) 12800000000000000000),
            (exactRationalLiteral (430094583347819) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (436420386686871197) 204800000000000000000),
            (exactRationalLiteral (8916323630838763) 12800000000000000000),
            (exactRationalLiteral (-136132483577169) 800000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (244168487133462619) 1228800000000000000000),
            (exactRationalLiteral (12075814955539479) 25600000000000000000),
            (exactRationalLiteral (189062045344103) 320000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-646028591669937041) 1228800000000000000000),
            (exactRationalLiteral (-21714040621553461) 25600000000000000000),
            (exactRationalLiteral (-2686241421212393) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1371118927013073019) 1228800000000000000000),
            (exactRationalLiteral (10171800861148277) 5120000000000000000),
            (exactRationalLiteral (9159718681050077) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (817595602075069) 6144000000000000000),
            (exactRationalLiteral (-37855370123806531) 3200000000000000000),
            (exactRationalLiteral (-209851525964291) 8000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-7784299117414843831) 614400000000000000000),
            (exactRationalLiteral (439998476656090797) 12800000000000000000),
            (exactRationalLiteral (15829047335548909) 160000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (13641934326229190227) 204800000000000000000),
            (exactRationalLiteral (24418306452576609) 2560000000000000000),
            (exactRationalLiteral (-153705109287461343) 800000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2663773713285944969) 38400000000000000000),
            (exactRationalLiteral (-185953103716996597) 1600000000000000000),
            (exactRationalLiteral (113669508984317) 625000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-348929071016489833) 614400000000000000000),
            (exactRationalLiteral (1540700453672173227) 12800000000000000000),
            (exactRationalLiteral (-57553725138164113) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1359943153677426013) 81920000000000000000),
            (exactRationalLiteral (-185408031475142589) 5120000000000000000),
            (exactRationalLiteral (-14960852265633) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (6159126082153113) 102400000000000000000),
            (exactRationalLiteral (-6159126082153113) 6400000000000000000),
            (exactRationalLiteral (2053042027384371) 400000000000000000),
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
          (exactRationalLiteral (80057884482759481) 9600000000000000000),
          (exactRationalLiteral (1456901038346811053) 19200000000000000000),
          (exactRationalLiteral (103051549437941341) 1536000000000000000),
          (exactRationalLiteral (138669066680526041) 9600000000000000000),
          (exactRationalLiteral (19331800776779) 25000000000000000),
          (exactRationalLiteral (23392933815085561) 19200000000000000000),
          (exactRationalLiteral (89936413834379227) 153600000000000000000),
          (exactRationalLiteral (35414517352355473) 153600000000000000000),
          (exactRationalLiteral (33389723650311181) 15360000000000000000),
          (exactRationalLiteral (69399287208207341) 76800000000000000000),
          (exactRationalLiteral (76634877863124161) 7680000000000000000),
          (exactRationalLiteral (1181644768851619) 256000000000000000),
          (exactRationalLiteral (7978422922746023) 3840000000000000000),
          (exactRationalLiteral (262321504538811131) 19200000000000000000),
          (exactRationalLiteral (889723549152499393) 19200000000000000000),
          (exactRationalLiteral (1164983255838906199) 9600000000000000000),
          (exactRationalLiteral (2755800093400664657) 2400000000000000000),
          (exactRationalLiteral (9674858865487824019) 6400000000000000000),
          (exactRationalLiteral (384190226287280617) 640000000000000000),
          (exactRationalLiteral (87996485054998637) 1920000000000000000),
          (exactRationalLiteral (10737065927302296949) 19200000000000000000),
          (exactRationalLiteral (5391527313489936847) 4800000000000000000),
          (exactRationalLiteral (10737065927302296949) 19200000000000000000),
          (exactRationalLiteral (87996485054998637) 1920000000000000000),
          (exactRationalLiteral (384190226287280617) 640000000000000000),
          (exactRationalLiteral (9674858865487824019) 6400000000000000000),
          (exactRationalLiteral (2755800093400664657) 2400000000000000000),
          (exactRationalLiteral (1164983255838906199) 9600000000000000000),
          (exactRationalLiteral (889723549152499393) 19200000000000000000),
          (exactRationalLiteral (262321504538811131) 19200000000000000000),
          (exactRationalLiteral (7978422922746023) 3840000000000000000),
          (exactRationalLiteral (1181644768851619) 256000000000000000),
          (exactRationalLiteral (76634877863124161) 7680000000000000000),
          (exactRationalLiteral (69399287208207341) 76800000000000000000),
          (exactRationalLiteral (33389723650311181) 15360000000000000000),
          (exactRationalLiteral (35414517352355473) 153600000000000000000),
          (exactRationalLiteral (89936413834379227) 153600000000000000000),
          (exactRationalLiteral (23392933815085561) 19200000000000000000),
          (exactRationalLiteral (19331800776779) 25000000000000000),
          (exactRationalLiteral (138669066680526041) 9600000000000000000),
          (exactRationalLiteral (103051549437941341) 1536000000000000000),
          (exactRationalLiteral (1456901038346811053) 19200000000000000000),
          (exactRationalLiteral (80057884482759481) 9600000000000000000),
          (exactRationalLiteral (24128906906535711) 1280000000000000000),
          (exactRationalLiteral (684347342461457) 4800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 5),
      (37, 13),
      (37, 21),
      (37, 29)
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
            (exactRationalLiteral (684347342461457) 307200000000000000000),
            (exactRationalLiteral (-684347342461457) 6400000000000000000),
            (exactRationalLiteral (684347342461457) 400000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (997756705574218023) 81920000000000000000),
            (exactRationalLiteral (-172433687499995541) 5120000000000000000),
            (exactRationalLiteral (6502132839839157) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (8044732944951419621) 614400000000000000000),
            (exactRationalLiteral (1230537550915936499) 12800000000000000000),
            (exactRationalLiteral (-97527726239954251) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-258295451309944751) 3200000000000000000),
            (exactRationalLiteral (-100239737874380289) 1600000000000000000),
            (exactRationalLiteral (12334780741908717) 50000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (39661729621306362187) 614400000000000000000),
            (exactRationalLiteral (-568809524641447651) 12800000000000000000),
            (exactRationalLiteral (-38349083832940801) 160000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4130873975715092213) 614400000000000000000),
            (exactRationalLiteral (6307401153457641) 102400000000000000),
            (exactRationalLiteral (95068097085312619) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3649431632702603) 2048000000000000000),
            (exactRationalLiteral (-60870314706458363) 3200000000000000000),
            (exactRationalLiteral (-6261184142218641) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-948600434779392097) 1228800000000000000000),
            (exactRationalLiteral (91221800143257537) 25600000000000000000),
            (exactRationalLiteral (11021679237707999) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-810642715468200227) 1228800000000000000000),
            (exactRationalLiteral (-6701299562719977) 5120000000000000000),
            (exactRationalLiteral (-3209987174810819) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (109547102898718379) 409600000000000000000),
            (exactRationalLiteral (16194160416826271) 25600000000000000000),
            (exactRationalLiteral (1113862503922881) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1361023212123111077) 614400000000000000000),
            (exactRationalLiteral (1664128747345111) 2560000000000000000),
            (exactRationalLiteral (-32341492695887) 160000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (204105781179534227) 204800000000000000000),
            (exactRationalLiteral (3892816791744899) 2560000000000000000),
            (exactRationalLiteral (421663484622249) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3106347780931491377) 307200000000000000000),
            (exactRationalLiteral (-2810940127616171) 1280000000000000000),
            (exactRationalLiteral (-405729220555169) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1824001536814279879) 409600000000000000000),
            (exactRationalLiteral (21744551733959621) 25600000000000000000),
            (exactRationalLiteral (-279679735787061) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1536817564405231543) 1228800000000000000000),
            (exactRationalLiteral (111377657316936487) 25600000000000000000),
            (exactRationalLiteral (-134928525693419) 320000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-584943599744753363) 49152000000000000000),
            (exactRationalLiteral (238044360433867803) 25600000000000000000),
            (exactRationalLiteral (-1537790612114843) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49015201177366305157) 1228800000000000000000),
            (exactRationalLiteral (883012327354905141) 25600000000000000000),
            (exactRationalLiteral (-93078390718381) 64000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-29221999195168653991) 614400000000000000000),
            (exactRationalLiteral (4417895075753432039) 12800000000000000000),
            (exactRationalLiteral (-252379359789307687) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1235325392089480229) 1536000000000000000),
            (exactRationalLiteral (-675911459958327077) 400000000000000000),
            (exactRationalLiteral (54171893458951127) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-438368054451679857691) 409600000000000000000),
            (exactRationalLiteral (57275091413178243057) 25600000000000000000),
            (exactRationalLiteral (-1943053503331030929) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (82252489899761331401) 204800000000000000000),
            (exactRationalLiteral (-2763988375335123471) 2560000000000000000),
            (exactRationalLiteral (333733875767161659) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10416934271434026581) 307200000000000000000),
            (exactRationalLiteral (728450500546368009) 6400000000000000000),
            (exactRationalLiteral (40502732269070083) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-591147683038090037197) 1228800000000000000000),
            (exactRationalLiteral (9221208368014708077) 25600000000000000000),
            (exactRationalLiteral (-362629413722450701) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (302200050563704944691) 307200000000000000000),
            (exactRationalLiteral (-172394318940553243) 256000000000000000),
            (exactRationalLiteral (126498710409410323) 400000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-591147683038090037197) 1228800000000000000000),
            (exactRationalLiteral (9221208368014708077) 25600000000000000000),
            (exactRationalLiteral (-362629413722450701) 1600000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10416934271434026581) 307200000000000000000),
            (exactRationalLiteral (728450500546368009) 6400000000000000000),
            (exactRationalLiteral (40502732269070083) 400000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (82252489899761331401) 204800000000000000000),
            (exactRationalLiteral (-2763988375335123471) 2560000000000000000),
            (exactRationalLiteral (333733875767161659) 800000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-438368054451679857691) 409600000000000000000),
            (exactRationalLiteral (57275091413178243057) 25600000000000000000),
            (exactRationalLiteral (-1943053503331030929) 1600000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1235325392089480229) 1536000000000000000),
            (exactRationalLiteral (-675911459958327077) 400000000000000000),
            (exactRationalLiteral (54171893458951127) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-29221999195168653991) 614400000000000000000),
            (exactRationalLiteral (4417895075753432039) 12800000000000000000),
            (exactRationalLiteral (-252379359789307687) 800000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-49015201177366305157) 1228800000000000000000),
            (exactRationalLiteral (883012327354905141) 25600000000000000000),
            (exactRationalLiteral (-93078390718381) 64000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-584943599744753363) 49152000000000000000),
            (exactRationalLiteral (238044360433867803) 25600000000000000000),
            (exactRationalLiteral (-1537790612114843) 1600000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1536817564405231543) 1228800000000000000000),
            (exactRationalLiteral (111377657316936487) 25600000000000000000),
            (exactRationalLiteral (-134928525693419) 320000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1824001536814279879) 409600000000000000000),
            (exactRationalLiteral (21744551733959621) 25600000000000000000),
            (exactRationalLiteral (-279679735787061) 1600000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3106347780931491377) 307200000000000000000),
            (exactRationalLiteral (-2810940127616171) 1280000000000000000),
            (exactRationalLiteral (-405729220555169) 400000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (204105781179534227) 204800000000000000000),
            (exactRationalLiteral (3892816791744899) 2560000000000000000),
            (exactRationalLiteral (421663484622249) 800000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1361023212123111077) 614400000000000000000),
            (exactRationalLiteral (1664128747345111) 2560000000000000000),
            (exactRationalLiteral (-32341492695887) 160000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (109547102898718379) 409600000000000000000),
            (exactRationalLiteral (16194160416826271) 25600000000000000000),
            (exactRationalLiteral (1113862503922881) 1600000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-810642715468200227) 1228800000000000000000),
            (exactRationalLiteral (-6701299562719977) 5120000000000000000),
            (exactRationalLiteral (-3209987174810819) 1600000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-948600434779392097) 1228800000000000000000),
            (exactRationalLiteral (91221800143257537) 25600000000000000000),
            (exactRationalLiteral (11021679237707999) 1600000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3649431632702603) 2048000000000000000),
            (exactRationalLiteral (-60870314706458363) 3200000000000000000),
            (exactRationalLiteral (-6261184142218641) 200000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-4130873975715092213) 614400000000000000000),
            (exactRationalLiteral (6307401153457641) 102400000000000000),
            (exactRationalLiteral (95068097085312619) 800000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (39661729621306362187) 614400000000000000000),
            (exactRationalLiteral (-568809524641447651) 12800000000000000000),
            (exactRationalLiteral (-38349083832940801) 160000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-258295451309944751) 3200000000000000000),
            (exactRationalLiteral (-100239737874380289) 1600000000000000000),
            (exactRationalLiteral (12334780741908717) 50000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (8044732944951419621) 614400000000000000000),
            (exactRationalLiteral (1230537550915936499) 12800000000000000000),
            (exactRationalLiteral (-97527726239954251) 800000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (997756705574218023) 81920000000000000000),
            (exactRationalLiteral (-172433687499995541) 5120000000000000000),
            (exactRationalLiteral (6502132839839157) 320000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 307200000000000000000),
            (exactRationalLiteral (-684347342461457) 6400000000000000000),
            (exactRationalLiteral (684347342461457) 400000000000000000),
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
          (exactRationalLiteral (684347342461457) 38400000000000000000),
          (exactRationalLiteral (146950792954004407) 10240000000000000000),
          (exactRationalLiteral (5578015341029527) 300000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (5101492761584401807) 76800000000000000000),
          (exactRationalLiteral (259121106133731407) 25600000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (148766472221796209) 153600000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (692244098113792573) 153600000000000000000),
          (exactRationalLiteral (234101731660052767) 153600000000000000000),
          (exactRationalLiteral (639234800569238089) 51200000000000000000),
          (exactRationalLiteral (2152839631410967407) 51200000000000000000),
          (exactRationalLiteral (5398369621902521863) 76800000000000000000),
          (exactRationalLiteral (2923798885288133467) 3200000000000000000),
          (exactRationalLiteral (186476910279321297601) 153600000000000000000),
          (exactRationalLiteral (36099880897357613059) 76800000000000000000),
          (exactRationalLiteral (1548581791721812691) 38400000000000000000),
          (exactRationalLiteral (25834137298110739647) 51200000000000000000),
          (exactRationalLiteral (39441665588772169051) 38400000000000000000),
          (exactRationalLiteral (25834137298110739647) 51200000000000000000),
          (exactRationalLiteral (1548581791721812691) 38400000000000000000),
          (exactRationalLiteral (36099880897357613059) 76800000000000000000),
          (exactRationalLiteral (186476910279321297601) 153600000000000000000),
          (exactRationalLiteral (2923798885288133467) 3200000000000000000),
          (exactRationalLiteral (5398369621902521863) 76800000000000000000),
          (exactRationalLiteral (2152839631410967407) 51200000000000000000),
          (exactRationalLiteral (639234800569238089) 51200000000000000000),
          (exactRationalLiteral (234101731660052767) 153600000000000000000),
          (exactRationalLiteral (692244098113792573) 153600000000000000000),
          (exactRationalLiteral (1537956456377611) 150000000000000000),
          (exactRationalLiteral (328110532382461) 300000000000000000),
          (exactRationalLiteral (225502479403141) 100000000000000000),
          (exactRationalLiteral (46466022167603) 150000000000000000),
          (exactRationalLiteral (224866709792537) 300000000000000000),
          (exactRationalLiteral (148766472221796209) 153600000000000000000),
          (exactRationalLiteral (92892444725641) 30000000000000000),
          (exactRationalLiteral (259121106133731407) 25600000000000000000),
          (exactRationalLiteral (5101492761584401807) 76800000000000000000),
          (exactRationalLiteral (25088125549168747) 300000000000000000),
          (exactRationalLiteral (5578015341029527) 300000000000000000),
          (exactRationalLiteral (146950792954004407) 10240000000000000000),
          (exactRationalLiteral (684347342461457) 38400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 4),
      (37, 12),
      (37, 20),
      (37, 28)
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
            (exactRationalLiteral (4693938421943133563) 2457600000000000000000),
            (exactRationalLiteral (-247049390628585977) 25600000000000000000),
            (exactRationalLiteral (13002599506767683) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (18129363624468668173) 655360000000000000000),
            (exactRationalLiteral (-38031948919980537) 4096000000000000000),
            (exactRationalLiteral (-42391030703212401) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-51517748084154577213) 983040000000000000000),
            (exactRationalLiteral (5777792428771960123) 51200000000000000000),
            (exactRationalLiteral (144723556885307671) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2290914485997955621) 614400000000000000000),
            (exactRationalLiteral (-228355309140579299) 1280000000000000000),
            (exactRationalLiteral (-5761617426142201) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (194290444379156072833) 4915200000000000000000),
            (exactRationalLiteral (5266625627372517077) 51200000000000000000),
            (exactRationalLiteral (-60148204372845383) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-22717382488049825213) 1638400000000000000000),
            (exactRationalLiteral (-1010076696178850899) 51200000000000000000),
            (exactRationalLiteral (54791880706296609) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1864083924966891337) 1228800000000000000000),
            (exactRationalLiteral (35626791840441749) 12800000000000000000),
            (exactRationalLiteral (-3895752342990671) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-11660365016704189451) 9830400000000000000000),
            (exactRationalLiteral (-23106737430808811) 20480000000000000000),
            (exactRationalLiteral (6216693743823661) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3929352487178651953) 9830400000000000000000),
            (exactRationalLiteral (1714375047552719) 20480000000000000000),
            (exactRationalLiteral (-1968135444035017) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (842910657391345387) 9830400000000000000000),
            (exactRationalLiteral (13389795456291063) 102400000000000000000),
            (exactRationalLiteral (795030651625651) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1794639714229890307) 983040000000000000000),
            (exactRationalLiteral (40583097867626363) 51200000000000000000),
            (exactRationalLiteral (-106027597789609) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1679741097083366939) 4915200000000000000000),
            (exactRationalLiteral (47964925114740183) 51200000000000000000),
            (exactRationalLiteral (914991308411843) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-4531779490676034023) 491520000000000000000),
            (exactRationalLiteral (-30291588045508959) 25600000000000000000),
            (exactRationalLiteral (-142734364799279) 160000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-48085123625361050167) 9830400000000000000000),
            (exactRationalLiteral (70010165806759021) 102400000000000000000),
            (exactRationalLiteral (1557479537990561) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-35396331274166826733) 9830400000000000000000),
            (exactRationalLiteral (444969760268684191) 102400000000000000000),
            (exactRationalLiteral (1381101080408411) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-54923713400932787491) 3276800000000000000000),
            (exactRationalLiteral (854090838884664083) 102400000000000000000),
            (exactRationalLiteral (8845381391924223) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-187072851354134084013) 3276800000000000000000),
            (exactRationalLiteral (2803663845724947421) 102400000000000000000),
            (exactRationalLiteral (47500123282664529) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1347315066818390321197) 4915200000000000000000),
            (exactRationalLiteral (21578239588020852287) 51200000000000000000),
            (exactRationalLiteral (274955232225255131) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (90076543442076010717) 51200000000000000000),
            (exactRationalLiteral (-575256696372215457) 400000000000000000),
            (exactRationalLiteral (-77855367243918567) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-20939695860609354921499) 9830400000000000000000),
            (exactRationalLiteral (88609717450085964953) 102400000000000000000),
            (exactRationalLiteral (12150262783287179933) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3311265682923596475001) 4915200000000000000000),
            (exactRationalLiteral (8649462942258575033) 10240000000000000000),
            (exactRationalLiteral (-6463178470239931823) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (290893851831976954141) 2457600000000000000000),
            (exactRationalLiteral (-26464000872131335767) 25600000000000000000),
            (exactRationalLiteral (1647100586892260293) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2609717546149215846693) 3276800000000000000000),
            (exactRationalLiteral (96252178527138261109) 102400000000000000000),
            (exactRationalLiteral (-2766937940500947351) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3635074912230662745409) 2457600000000000000000),
            (exactRationalLiteral (-32836327570970764411) 25600000000000000000),
            (exactRationalLiteral (664467030764440537) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2609717546149215846693) 3276800000000000000000),
            (exactRationalLiteral (96252178527138261109) 102400000000000000000),
            (exactRationalLiteral (-2766937940500947351) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (290893851831976954141) 2457600000000000000000),
            (exactRationalLiteral (-26464000872131335767) 25600000000000000000),
            (exactRationalLiteral (1647100586892260293) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3311265682923596475001) 4915200000000000000000),
            (exactRationalLiteral (8649462942258575033) 10240000000000000000),
            (exactRationalLiteral (-6463178470239931823) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20939695860609354921499) 9830400000000000000000),
            (exactRationalLiteral (88609717450085964953) 102400000000000000000),
            (exactRationalLiteral (12150262783287179933) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (90076543442076010717) 51200000000000000000),
            (exactRationalLiteral (-575256696372215457) 400000000000000000),
            (exactRationalLiteral (-77855367243918567) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-1347315066818390321197) 4915200000000000000000),
            (exactRationalLiteral (21578239588020852287) 51200000000000000000),
            (exactRationalLiteral (274955232225255131) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-187072851354134084013) 3276800000000000000000),
            (exactRationalLiteral (2803663845724947421) 102400000000000000000),
            (exactRationalLiteral (47500123282664529) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-54923713400932787491) 3276800000000000000000),
            (exactRationalLiteral (854090838884664083) 102400000000000000000),
            (exactRationalLiteral (8845381391924223) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-35396331274166826733) 9830400000000000000000),
            (exactRationalLiteral (444969760268684191) 102400000000000000000),
            (exactRationalLiteral (1381101080408411) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-48085123625361050167) 9830400000000000000000),
            (exactRationalLiteral (70010165806759021) 102400000000000000000),
            (exactRationalLiteral (1557479537990561) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4531779490676034023) 491520000000000000000),
            (exactRationalLiteral (-30291588045508959) 25600000000000000000),
            (exactRationalLiteral (-142734364799279) 160000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1679741097083366939) 4915200000000000000000),
            (exactRationalLiteral (47964925114740183) 51200000000000000000),
            (exactRationalLiteral (914991308411843) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (1794639714229890307) 983040000000000000000),
            (exactRationalLiteral (40583097867626363) 51200000000000000000),
            (exactRationalLiteral (-106027597789609) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (842910657391345387) 9830400000000000000000),
            (exactRationalLiteral (13389795456291063) 102400000000000000000),
            (exactRationalLiteral (795030651625651) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3929352487178651953) 9830400000000000000000),
            (exactRationalLiteral (1714375047552719) 20480000000000000000),
            (exactRationalLiteral (-1968135444035017) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-11660365016704189451) 9830400000000000000000),
            (exactRationalLiteral (-23106737430808811) 20480000000000000000),
            (exactRationalLiteral (6216693743823661) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1864083924966891337) 1228800000000000000000),
            (exactRationalLiteral (35626791840441749) 12800000000000000000),
            (exactRationalLiteral (-3895752342990671) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-22717382488049825213) 1638400000000000000000),
            (exactRationalLiteral (-1010076696178850899) 51200000000000000000),
            (exactRationalLiteral (54791880706296609) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (194290444379156072833) 4915200000000000000000),
            (exactRationalLiteral (5266625627372517077) 51200000000000000000),
            (exactRationalLiteral (-60148204372845383) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2290914485997955621) 614400000000000000000),
            (exactRationalLiteral (-228355309140579299) 1280000000000000000),
            (exactRationalLiteral (-5761617426142201) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-51517748084154577213) 983040000000000000000),
            (exactRationalLiteral (5777792428771960123) 51200000000000000000),
            (exactRationalLiteral (144723556885307671) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (18129363624468668173) 655360000000000000000),
            (exactRationalLiteral (-38031948919980537) 4096000000000000000),
            (exactRationalLiteral (-42391030703212401) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (4693938421943133563) 2457600000000000000000),
            (exactRationalLiteral (-247049390628585977) 25600000000000000000),
            (exactRationalLiteral (13002599506767683) 800000000000000000),
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
          (exactRationalLiteral (684347342461457) 307200000000000000),
          (exactRationalLiteral (285563221188802203) 10240000000000000000),
          (exactRationalLiteral (4288561875560655443) 76800000000000000000),
          (exactRationalLiteral (44767873088764909) 4800000000000000000),
          (exactRationalLiteral (8745452353884019441) 204800000000000000000),
          (exactRationalLiteral (8876255060045419309) 614400000000000000000),
          (exactRationalLiteral (244846199432836111) 153600000000000000000),
          (exactRationalLiteral (1498423127082065209) 1228800000000000000000),
          (exactRationalLiteral (61886103849175759) 153600000000000000000),
          (exactRationalLiteral (110693676481712089) 1228800000000000000000),
          (exactRationalLiteral (378942374769542111) 204800000000000000000),
          (exactRationalLiteral (228297078850432529) 614400000000000000000),
          (exactRationalLiteral (2843989873142829257) 307200000000000000000),
          (exactRationalLiteral (251512276897008419) 51200000000000000000),
          (exactRationalLiteral (114771677002408231) 30720000000000000000),
          (exactRationalLiteral (2614158989721586159) 153600000000000000000),
          (exactRationalLiteral (8898187146013397177) 153600000000000000000),
          (exactRationalLiteral (881986908974500259) 3072000000000000000),
          (exactRationalLiteral (17305711141969359497) 9600000000000000000),
          (exactRationalLiteral (110250681816352886783) 51200000000000000000),
          (exactRationalLiteral (17110187707122533659) 24576000000000000000),
          (exactRationalLiteral (5864363741430299393) 38400000000000000000),
          (exactRationalLiteral (126973907603467521929) 153600000000000000000),
          (exactRationalLiteral (58368773439540172559) 38400000000000000000),
          (exactRationalLiteral (126973907603467521929) 153600000000000000000),
          (exactRationalLiteral (5864363741430299393) 38400000000000000000),
          (exactRationalLiteral (17110187707122533659) 24576000000000000000),
          (exactRationalLiteral (110250681816352886783) 51200000000000000000),
          (exactRationalLiteral (17305711141969359497) 9600000000000000000),
          (exactRationalLiteral (881986908974500259) 3072000000000000000),
          (exactRationalLiteral (8898187146013397177) 153600000000000000000),
          (exactRationalLiteral (2614158989721586159) 153600000000000000000),
          (exactRationalLiteral (114771677002408231) 30720000000000000000),
          (exactRationalLiteral (251512276897008419) 51200000000000000000),
          (exactRationalLiteral (2843989873142829257) 307200000000000000000),
          (exactRationalLiteral (228297078850432529) 614400000000000000000),
          (exactRationalLiteral (378942374769542111) 204800000000000000000),
          (exactRationalLiteral (110693676481712089) 1228800000000000000000),
          (exactRationalLiteral (61886103849175759) 153600000000000000000),
          (exactRationalLiteral (1498423127082065209) 1228800000000000000000),
          (exactRationalLiteral (244846199432836111) 153600000000000000000),
          (exactRationalLiteral (8876255060045419309) 614400000000000000000),
          (exactRationalLiteral (8745452353884019441) 204800000000000000000),
          (exactRationalLiteral (44767873088764909) 4800000000000000000),
          (exactRationalLiteral (4288561875560655443) 76800000000000000000),
          (exactRationalLiteral (285563221188802203) 10240000000000000000),
          (exactRationalLiteral (684347342461457) 307200000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 57),
      (28, 9),
      (28, 25),
      (28, 41)
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
theorem generatorCoordinates19_valid : ∀ i, (generatorCoordinates19 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
